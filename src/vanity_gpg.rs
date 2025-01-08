use clap::ValueEnum;
use byteorder::{ByteOrder, BigEndian};
use rand::{Rng, CryptoRng};
use pgp::{
    composed::{key::SecretKeyParamsBuilder, KeyType},
    crypto::{
        hash::HashAlgorithm,
        sym::SymmetricKeyAlgorithm,
        ecc_curve::ECCCurve,
    },
    ser::Serialize,
    packet::KeyFlags,
    types::{
        CompressionAlgorithm,
        PublicKeyTrait,
        SecretKeyTrait,
        KeyVersion,
    },
    Deserializable,
    SecretKey,
    SecretSubkey,
    SignedSecretKey,
    SubkeyParamsBuilder,
};
use smallvec::smallvec;
use log::debug;

/// 获取用于计算一个私钥的指纹的数据
fn build_secret_key_hashdata(secret_key: impl SecretKeyTrait) -> Vec<u8> {
    let mut hashdata = vec![0x99, 0, 0, 0x04, 0, 0, 0, 0];
    BigEndian::write_u32(&mut hashdata[4..8], secret_key.created_at().timestamp() as u32);
    hashdata.push(secret_key.algorithm().into());
    secret_key.public_params().to_writer(&mut hashdata).unwrap();
    let packet_len = (hashdata.len() - 3) as u16;
    BigEndian::write_u16(&mut hashdata[1..3], packet_len);
    hashdata
}

/// 需要被修改的密钥类型
#[derive(ValueEnum, Default, Clone, Copy, Debug)]
#[clap(rename_all = "kebab_case")]
pub enum CipherSuite {
    #[default]
    Ed25519,
    Cv25519,
    RSA2048,
    RSA3072,
    RSA4096,
    EcdhP256,
    EcdhP384,
    EcdhP521,
    EcdsaP256,
    EcdsaP384,
    EcdsaP521,
}
pub struct VanitySecretKey {
    pub cipher_suite: CipherSuite,
    pub secret_key: SignedSecretKey,
}

impl VanitySecretKey {
    pub fn new(cipher_suite: CipherSuite, user_id: String, mut rng: impl Rng + CryptoRng) -> Self {
        let mut secret_key_params_builder = SecretKeyParamsBuilder::default();
        secret_key_params_builder
            .preferred_symmetric_algorithms(smallvec![
                SymmetricKeyAlgorithm::AES256,
                SymmetricKeyAlgorithm::AES192,
                SymmetricKeyAlgorithm::AES128,
            ])
            .preferred_hash_algorithms(smallvec![
                HashAlgorithm::SHA2_512,
                HashAlgorithm::SHA2_384,
                HashAlgorithm::SHA2_256,
                HashAlgorithm::SHA2_224,
            ])
            .preferred_compression_algorithms(smallvec![
                CompressionAlgorithm::ZLIB,
                CompressionAlgorithm::BZip2,
                CompressionAlgorithm::ZIP,
                CompressionAlgorithm::Uncompressed,
            ])
            .can_certify(true)
            .can_sign(true)
            .primary_user_id(user_id);

        match cipher_suite {
            CipherSuite::Cv25519 | CipherSuite::Ed25519 => {
                let mut subkey_params_builder = SubkeyParamsBuilder::default();
                subkey_params_builder
                    .key_type(KeyType::ECDH(ECCCurve::Curve25519))
                    .can_encrypt(true);
                secret_key_params_builder
                    .key_type(KeyType::EdDSALegacy)
                    .subkey(subkey_params_builder.build().unwrap());
            },
                CipherSuite::EcdhP256 | CipherSuite::EcdsaP256 |
                CipherSuite::EcdhP384 | CipherSuite::EcdsaP384 |
                CipherSuite::EcdhP521 | CipherSuite::EcdsaP521 => {
                let curve = match cipher_suite {
                    CipherSuite::EcdhP256 | CipherSuite::EcdsaP256 => ECCCurve::P256,
                    CipherSuite::EcdhP384 | CipherSuite::EcdsaP384 => ECCCurve::P384,
                    CipherSuite::EcdhP521 | CipherSuite::EcdsaP521 => ECCCurve::P521,
                    _ => unreachable!(),
                };
                let mut subkey_params_builder = SubkeyParamsBuilder::default();
                subkey_params_builder
                    .key_type(KeyType::ECDH(curve.clone()))
                    .can_encrypt(true);
                secret_key_params_builder
                    .key_type(KeyType::ECDSA(curve.clone()))
                    .subkey(subkey_params_builder.build().unwrap());
            },
            CipherSuite::RSA2048 | CipherSuite::RSA3072 | CipherSuite::RSA4096 => {
                let bits = match cipher_suite {
                    CipherSuite::RSA2048 => 2048,
                    CipherSuite::RSA3072 => 3072,
                    CipherSuite::RSA4096 => 4096,
                    _ => unreachable!(),
                };
                secret_key_params_builder
                    .key_type(KeyType::Rsa(bits))
                    .can_encrypt(true);
            },
        }

        let secret_key_params = secret_key_params_builder.build().unwrap();
        let secret_key = secret_key_params
            .generate(&mut rng).unwrap()
            .sign(&mut rng, || String::new()).unwrap();
        assert_eq!(secret_key.version(), KeyVersion::V4);

        Self {
            cipher_suite,
            secret_key,
        }
    }

    pub fn edit_timestamp(&mut self, timestamp: u32, mut rng: impl Rng + CryptoRng) {
        // RFC 9580 - OpenPGP
        // 4. Packet Syntax
        // https://datatracker.ietf.org/doc/html/rfc9580#name-packet-syntax
        let mut secret_key_bytes = Vec::from(self.secret_key.to_bytes().unwrap());
        let mut packet_read_pos: usize = 0;
        while packet_read_pos < secret_key_bytes.len() {
            let cipher_type_byte = secret_key_bytes[packet_read_pos];
            debug!("cipher_type_byte = {:#04X}", cipher_type_byte);
            packet_read_pos += 1;
            let (size, size_length) = match cipher_type_byte >> 6 {
                0b10 => match cipher_type_byte & 0b00000011 {
                    0 => (secret_key_bytes[packet_read_pos] as usize, 1),
                    1 => (BigEndian::read_u16(&secret_key_bytes[packet_read_pos..packet_read_pos + 2]) as usize, 2),
                    2 => (BigEndian::read_u32(&secret_key_bytes[packet_read_pos..packet_read_pos + 4]) as usize, 4),
                    3 => unimplemented!("Indeterminate length"),
                    _ => unreachable!(),
                },
                0b11 => match secret_key_bytes[packet_read_pos] {
                    x if x < 192 => (secret_key_bytes[packet_read_pos] as usize, 1),
                    x if x < 224 => ((((secret_key_bytes[packet_read_pos] - 192) as usize) << 8) + (secret_key_bytes[packet_read_pos + 1] as usize) + 192, 2),
                    x if x == 255 => (BigEndian::read_u32(&secret_key_bytes[packet_read_pos + 1..packet_read_pos + 5]) as usize, 5),
                    _ => unimplemented!("Partial body length"),
                },
                _ => unreachable!(),
            };
            debug!("size = {size}, size_length = {size_length}");
            packet_read_pos += size_length;
            let packet_type = match cipher_type_byte >> 6 {
                0b10 => (cipher_type_byte & 0b00111100) >> 2,
                0b11 => cipher_type_byte & 0b00111111,
                _ => unreachable!(),
            };
            debug!("packet_type = {packet_type:#04X}");
            // 0x05 => Secret-Key Packet
            // 0x07 => Secret-Subkey Packet
            if [0x05, 0x07].contains(&packet_type) {
                BigEndian::write_u32(&mut secret_key_bytes[packet_read_pos + 1..packet_read_pos + 5], timestamp);
            }
            packet_read_pos += size;
        }
        // 只修改了时间，因此这个key的签名是无效的
        let edited_key = SignedSecretKey::from_bytes(&secret_key_bytes[..]).unwrap();

        // 重新对key签名
        let mut subkey_flags = KeyFlags::default();
        subkey_flags.set_encrypt_storage(true);
        subkey_flags.set_encrypt_comms(true);
        self.secret_key = SecretKey::new(
            edited_key.primary_key,
            edited_key.details.as_unsigned(),
            edited_key.public_subkeys
                .iter()
                .map(|e| e.as_unsigned())
                .collect(),
            edited_key.secret_subkeys
                .iter()
                .map(|e| SecretSubkey::new(e.key.clone(), subkey_flags))
                .collect(),
        ).sign(&mut rng, || String::new()).unwrap();
        // self.secret_key.verify().unwrap();
    }

    pub fn hashdata(&self) -> Vec<u8> {
        match self.cipher_suite {
            CipherSuite::Ed25519 |
            CipherSuite::EcdsaP256 | CipherSuite::EcdsaP384 | CipherSuite::EcdsaP521 |
            CipherSuite::RSA2048 | CipherSuite::RSA3072 | CipherSuite::RSA4096
                => build_secret_key_hashdata(&self.secret_key),
            CipherSuite::Cv25519 |
            CipherSuite::EcdhP256 | CipherSuite::EcdhP384 | CipherSuite::EcdhP521
                => build_secret_key_hashdata(&self.secret_key.secret_subkeys[0]),
        }
    }

    pub fn to_armored_string(&self) -> Result<String, pgp::errors::Error> {
        self.secret_key.to_armored_string(pgp::ArmorOptions::default())
    }
}
