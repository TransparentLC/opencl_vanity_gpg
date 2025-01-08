use clap::{Parser, ValueEnum};
use std::sync::LazyLock;

pub static ARGS: LazyLock<Args> = LazyLock::new(if cfg!(debug_assertions) {
    Args::default
} else {
    Args::parse
});

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
pub struct Args {
    /// Cipher suite of the vanity key
    /// ed25519, ecdsa-****, rsa**** => Primary key
    /// cv25519,  ecdh-****          => Subkey
    /// Use gpg CLI for further editing of the key.
    #[arg(short, long, default_value_t, value_enum, verbatim_doc_comment)]
    pub cipher_suite: CipherSuite,

    /// OpenPGP compatible user ID
    #[arg(short, long, default_value_t = String::from("Dummy <dummy@example.com>"), verbatim_doc_comment)]
    pub user_id: String,

    /// A pattern less than 40 chars for matching fingerprints
    /// Format:
    /// * 0-9A-F are fixed, G-Z are wildcards
    /// * Other chars will be ignored
    /// * Case insensitive
    ///
    /// ## Example:
    ///
    /// * 11XXXX** may output a fingerprint ends with 11222234 or 11AAAABF
    /// * 11XXYYZZ may output a fingerprint ends with 11223344 or 11AABBCC
    #[arg(short, long, verbatim_doc_comment)]
    pub pattern: Option<String>,

    /// OpenCL kernel function for uint h[5] for matching fingerprints
    /// Ignore the pattern and no estimate is given if this has been set
    ///
    /// ## Example:
    ///
    /// * (h[4] & 0xFFFF)     == 0x1234     outputs a fingerprint ends with 1234
    /// * (h[0] & 0xFFFF0000) == 0xABCD0000 outputs a fingerprint starts with ABCD
    #[arg(short, long, verbatim_doc_comment)]
    pub filter: Option<String>,

    /// The dir where the vanity keys are saved
    #[arg(short, long)]
    pub output: Option<String>,

    /// Device ID to use
    #[arg(short, long)]
    pub device: Option<usize>,

    /// Adjust it to maximum your device's usage
    #[arg(short, long)]
    pub thread: Option<usize>,

    /// Adjust it to maximum your device's usage
    #[arg(short, long, default_value_t = 1 << 9)]
    pub iteration: usize,

    /// Exit after a specified time in seconds
    #[arg(long)]
    pub timeout: Option<f64>,

    /// Exit after getting a vanity key
    #[arg(long, default_value_t = false)]
    pub oneshot: bool,

    /// Don't print progress
    #[arg(long, default_value_t = false)]
    pub no_progress: bool,

    /// Don't print armored secret key
    #[arg(long, default_value_t = false)]
    pub no_secret_key_logging: bool,

    /// Show available OpenCL devices then exit
    #[arg(long, default_value_t = false)]
    pub list_device: bool,
}

impl Default for Args {
    fn default() -> Self {
        Self {
            cipher_suite: CipherSuite::Ed25519,
            user_id: String::from("Dummy <dummy@example.com>"),
            pattern: Some(String::from("XXXYYYZZZWWW")),
            filter: None,
            output: None,
            device: None,
            thread: None,
            iteration: 512,
            timeout: None,
            oneshot: true,
            no_progress: true,
            no_secret_key_logging: false,
            list_device: false,
        }
    }
}

/// Cipher Suites
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
