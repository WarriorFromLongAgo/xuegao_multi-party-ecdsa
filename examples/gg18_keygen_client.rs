#![allow(non_snake_case)]
/// to run:
/// 1: go to rocket_server -> cargo run
/// 2: cargo run from PARTIES number of terminals
/// 运行步骤:
/// 1: 进入 rocket_server 目录并运行 cargo run
/// 2: 在多个终端中运行 cargo run
use curv::{
    arithmetic::traits::Converter,
    cryptographic_primitives::{
        proofs::sigma_dlog::DLogProof, secret_sharing::feldman_vss::VerifiableSS,
    },
    elliptic::curves::{secp256_k1::Secp256k1, Point, Scalar},
    BigInt,
};
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2018::party_i::{
    KeyGenBroadcastMessage1, KeyGenDecommitMessage1, Keys, Parameters,
};
use paillier::EncryptionKey;
use reqwest::Client;
use sha2::Sha256;
use std::{env, fs, time};

mod common;
use common::{
    aes_decrypt, aes_encrypt, broadcast, poll_for_broadcasts, poll_for_p2p, postb, sendp2p, Params,
    PartySignup, AEAD, AES_KEY_BYTES_LEN,
};

fn main() {
    // 检查命令行参数数量
    if env::args().nth(3).is_some() {
        panic!("too many arguments")
    }
    if env::args().nth(2).is_none() {
        panic!("too few arguments")
    }
    //read parameters:
    // 读取配置文件 "params.json"
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    // 总份数
    let PARTIES: u16 = params.parties.parse::<u16>().unwrap();
    // 最小恢复份数
    let THRESHOLD: u16 = params.threshold.parse::<u16>().unwrap();

    let client = Client::new();

    // delay:
    // 设置延迟时间
    let delay = time::Duration::from_millis(25);
    let params = Parameters {
        threshold: THRESHOLD,
        share_count: PARTIES,
    };

    //signup:
    // 注册参与方
    let (party_num_int, uuid) = match signup(&client).unwrap() {
        PartySignup { number, uuid } => (number, uuid),
    };
    println!("number: {:?}, uuid: {:?}", party_num_int, uuid);

    // 生成密钥对
    let party_keys = Keys::create(party_num_int);
    let (bc_i, decom_i) = party_keys.phase1_broadcast_phase3_proof_of_correct_key();

    // 发送第一轮广播消息
    // send commitment to ephemeral public keys, get round 1 commitments of other parties
    assert!(broadcast(
        &client,
        party_num_int,
        "round1",
        serde_json::to_string(&bc_i).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round1_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES,
        delay,
        "round1",
        uuid.clone(),
    );

    // 收集并处理第一轮广播消息
    let mut bc1_vec = round1_ans_vec
        .iter()
        .map(|m| serde_json::from_str::<KeyGenBroadcastMessage1>(m).unwrap())
        .collect::<Vec<_>>();

    bc1_vec.insert(party_num_int as usize - 1, bc_i);

    // 发送第二轮广播消息
    // send ephemeral public keys and check commitments correctness
    assert!(broadcast(
        &client,
        party_num_int,
        "round2",
        serde_json::to_string(&decom_i).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round2_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES,
        delay,
        "round2",
        uuid.clone(),
    );

    // 收集并处理第二轮广播消息
    let mut j = 0;
    // 存储所有参与方的公钥点。
    let mut point_vec: Vec<Point<Secp256k1>> = Vec::new();
    // 存储所有参与方的解密消息。
    let mut decom_vec: Vec<KeyGenDecommitMessage1> = Vec::new();
    // 存储对称加密密钥，用于加密秘密共享。
    let mut enc_keys: Vec<Vec<u8>> = Vec::new();
    for i in 1..=PARTIES {
        if i == party_num_int {
            // 如果当前参与方是自己（i == party_num_int），则将自己的解密信息添加到 point_vec 和 decom_vec 中。
            point_vec.push(decom_i.y_i.clone());
            decom_vec.push(decom_i.clone());
        } else {
            // 从 round2_ans_vec 中解析出其他参与方的解密消息 decom_j。
            let decom_j: KeyGenDecommitMessage1 = serde_json::from_str(&round2_ans_vec[j]).unwrap();
            // 将其他参与方的公钥点 y_i 添加到 point_vec 中。
            point_vec.push(decom_j.y_i.clone());
            // 将其他参与方的解密消息 decom_j 添加到 decom_vec 中。
            decom_vec.push(decom_j.clone());
            // 计算对称加密密钥 key_bn，用于加密秘密共享：
            let key_bn: BigInt = (decom_j.y_i.clone() * party_keys.u_i.clone())
                .x_coord()
                .unwrap();
            // key_bn 是当前参与方的私钥 u_i 和其他参与方的公钥 y_i 的乘积的 x 坐标。
            let key_bytes = BigInt::to_bytes(&key_bn);
            // 创建一个长度为 AES_KEY_BYTES_LEN 的字节数组 template，并将 key_bytes 填充到 template 中。
            let mut template: Vec<u8> = vec![0u8; AES_KEY_BYTES_LEN - key_bytes.len()];
            // 将 key_bn 转换为字节数组 key_bytes。
            template.extend_from_slice(&key_bytes[..]);
            // 将 template 添加到 enc_keys 中。
            enc_keys.push(template);
            j += 1;
        }
    }

    // 计算所有参与方公钥的和
    // 将 point_vec 分为 head 和 tail 两部分，head 包含第一个元素，tail 包含剩余的元素。
    let (head, tail) = point_vec.split_at(1);
    // 使用 fold 函数计算所有参与方公钥的和 y_sum。
    let y_sum = tail.iter().fold(head[0].clone(), |acc, x| acc + x);

    // 第三轮广播信息 发送加密的秘密共享
    // 验证承诺消息和解密消息的正确性，并分发秘密共享。
    // 调用 party_keys.phase1_verify_com_phase3_verify_correct_key_phase2_distribute 方法，验证承诺消息和解密消息的正确性，并分发秘密共享。
    // 该方法返回 VSS 承诺 vss_scheme、秘密共享 secret_shares 和索引 _index。
    let (vss_scheme, secret_shares, _index) = party_keys
        .phase1_verify_com_phase3_verify_correct_key_phase2_distribute(
            &params, &decom_vec, &bc1_vec,
        )
        .expect("invalid key");

    //////////////////////////////////////////////////////////////////////////////
    // 发送加密的秘密共享
    let mut j = 0;
    for (k, i) in (1..=PARTIES).enumerate() {
        if i != party_num_int {
            // prepare encrypted ss for party i:
            // 获取对称加密密钥 key_i。
            let key_i = &enc_keys[j];
            // 将秘密共享 secret_shares[k] 转换为字节数组 plaintext。
            let plaintext = BigInt::to_bytes(&secret_shares[k].to_bigint());
            // 使用对称加密密钥 key_i 加密 plaintext，生成加密包 aead_pack_i。
            let aead_pack_i = aes_encrypt(key_i, &plaintext);
            // 通过点对点通信发送加密包 aead_pack_i 给其他参与方 i。
            assert!(sendp2p(
                &client,
                party_num_int,
                i,
                "round3",
                serde_json::to_string(&aead_pack_i).unwrap(),
                uuid.clone()
            )
            .is_ok());
            j += 1;
        }
    }

    // 收集并解密其他参与方的秘密共享
    let round3_ans_vec = poll_for_p2p(
        &client,
        party_num_int,
        PARTIES,
        delay,
        "round3",
        uuid.clone(),
    );

    let mut j = 0;
    let mut party_shares: Vec<Scalar<Secp256k1>> = Vec::new();
    for i in 1..=PARTIES {
        if i == party_num_int {
            party_shares.push(secret_shares[(i - 1) as usize].clone());
        } else {
            // 从 round3_ans_vec 中解析出加密包 aead_pack。
            let aead_pack: AEAD = serde_json::from_str(&round3_ans_vec[j]).unwrap();
            // 从 enc_keys 中获取对应的对称加密密钥 key_i。
            let key_i = &enc_keys[j];
            // 使用对称加密密钥 key_i 解密加密包 aead_pack，得到解密后的字节数组 out。
            let out = aes_decrypt(key_i, aead_pack);
            // 将解密后的字节数组 out 转换为大整数 out_bn。
            let out_bn = BigInt::from_bytes(&out[..]);
            // 将大整数 out_bn 转换为椭圆曲线标量 out_fe。
            let out_fe = Scalar::<Secp256k1>::from(&out_bn);
            // 将解密后的秘密共享 out_fe 添加到 party_shares 向量中。
            party_shares.push(out_fe);

            j += 1;
        }
    }

    // 发送第四轮广播消息
    // round 4: send vss commitments
    assert!(broadcast(
        &client,
        party_num_int,
        "round4",
        serde_json::to_string(&vss_scheme).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round4_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        PARTIES,
        delay,
        "round4",
        uuid.clone(),
    );

    // 收集并处理第四轮广播消息
    let mut j = 0;
    let mut vss_scheme_vec: Vec<VerifiableSS<Secp256k1>> = Vec::new();
    for i in 1..=PARTIES {
        if i == party_num_int {
            vss_scheme_vec.push(vss_scheme.clone());
        } else {
            let vss_scheme_j: VerifiableSS<Secp256k1> =
                serde_json::from_str(&round4_ans_vec[j]).unwrap();
            vss_scheme_vec.push(vss_scheme_j);
            j += 1;
        }
    }

    // 生成共享密钥和DLog证明
    let (shared_keys, dlog_proof) = party_keys
        .phase2_verify_vss_construct_keypair_phase3_pok_dlog(
            &params,
            &point_vec,
            &party_shares,
            &vss_scheme_vec,
            party_num_int,
        )
        .expect("invalid vss");

    // 发送第五轮广播消息
    // round 5: send dlog proof
    assert!(broadcast(
        &client,
        party_num_int,
        "round5",
        serde_json::to_string(&dlog_proof).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round5_ans_vec =
        poll_for_broadcasts(&client, party_num_int, PARTIES, delay, "round5", uuid);

    // 收集并验证DLog证明
    let mut j = 0;
    let mut dlog_proof_vec: Vec<DLogProof<Secp256k1, Sha256>> = Vec::new();
    for i in 1..=PARTIES {
        if i == party_num_int {
            dlog_proof_vec.push(dlog_proof.clone());
        } else {
            let dlog_proof_j: DLogProof<Secp256k1, Sha256> =
                serde_json::from_str(&round5_ans_vec[j]).unwrap();
            dlog_proof_vec.push(dlog_proof_j);
            j += 1;
        }
    }
    Keys::verify_dlog_proofs(&params, &dlog_proof_vec, &point_vec).expect("bad dlog proof");

    //save key to file:
    let paillier_key_vec = (0..PARTIES)
        .map(|i| bc1_vec[i as usize].e.clone())
        .collect::<Vec<EncryptionKey>>();

    // 将密钥保存到文件
    let keygen_json = serde_json::to_string(&(
        party_keys,
        shared_keys,
        party_num_int,
        vss_scheme_vec,
        paillier_key_vec,
        y_sum,
    ))
    .unwrap();
    fs::write(env::args().nth(2).unwrap(), keygen_json).expect("Unable to save !");
}

pub fn signup(client: &Client) -> Result<PartySignup, ()> {
    let key = "signup-keygen".to_string();

    let res_body = postb(client, "signupkeygen", key).unwrap();
    serde_json::from_str(&res_body).unwrap()
}
