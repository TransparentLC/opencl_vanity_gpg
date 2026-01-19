# opencl_vanity_gpg

使用 GPU（OpenCL）快速生成带有“靓号”的 PGP 密钥！

“靓号”指的是带有连号等特定格式的密钥指纹或 ID（例如以 `77777777` 结尾），具体介绍和生成原理请参见：

- [一位 PGP 进步青年的科学算号实践](https://www.douban.com/note/763978955/)
- [某科学的 PGP 算号指南](https://blog.dejavu.moe/posts/the-scientific-vanity-pgp-counting-guide/)

![](https://github.com/user-attachments/assets/e6364d93-fffe-4fcd-9857-b70155e6f476)

简单来说，密钥指纹是密钥生效时间和公钥内容的 SHA-1，通过不断生成密钥和修改时间（成本更低）的暴力遍历方式找到“靓号”。

> [!TIP]
>
> 姊妹项目：使用 WebGL 实现的网页版 [TransparentLC/webgl-vanity-gpg](https://github.com/TransparentLC/webgl-vanity-gpg)
>
> 实际上这个项目也可以当成是它的“锈化”版…\_φ(･ω･` )

目前最好的同类工具是使用 CPU 的 [RedL0tus/VanityGPG](https://github.com/RedL0tus/VanityGPG) 和使用 GPU（CUDA）的 [cuihaoleo/gpg-fingerprint-filter-gpu](https://github.com/cuihaoleo/gpg-fingerprint-filter-gpu)。这个项目是使用 GPU（OpenCL）实现的，优点当然是开箱即用了。

GitHub Actions 有自动编译好的二进制文件。

> [!NOTE]
>
> 如果你生成了指纹以 `00000000` 结尾的私钥，由于 GnuPG 的一个 bug，它们将无法正常显示信任等级，但是仍然可以使用。相关讨论见 [Issue #5](https://github.com/TransparentLC/opencl_vanity_gpg/issues/5)。

# 使用方法

```console
$ opencl_vanity_gpg -h
Usage: opencl_vanity_gpg [OPTIONS]

Options:
  -c, --cipher-suite <CIPHER_SUITE>
          Cipher suite of the vanity key
          ed25519, ecdsa-****, rsa**** => Primary key
          cv25519,  ecdh-****          => Subkey
          Use gpg CLI for further editing of the key. [default: ed25519] [possible values: ed25519, cv25519, rsa2048, rsa3072, rsa4096, ecdh-p256, ecdh-p384, ecdh-p521, ecdsa-p256, ecdsa-p384, ecdsa-p521]
  -u, --user-id <USER_ID>
          OpenPGP compatible user ID [default: "Dummy <dummy@example.com>"]
  -p, --pattern <PATTERN>
          A pattern less than 40 chars for matching fingerprints
          > Format:
          * 0-9A-F are fixed, G-Z are wildcards
          * Other chars will be ignored
          * Case insensitive
          > Example:
          * 11XXXX** may output a fingerprint ends with 11222234 or 11AAAABF
          * 11XXYYZZ may output a fingerprint ends with 11223344 or 11AABBCC
  -f, --filter <FILTER>
          OpenCL kernel function for uint h[5] for matching fingerprints
          Ignore the pattern and no estimate is given if this has been set
          > Example:
          * (h[4] & 0xFFFF)     == 0x1234     outputs a fingerprint ends with 1234
          * (h[0] & 0xFFFF0000) == 0xABCD0000 outputs a fingerprint starts with ABCD
  -o, --output <OUTPUT>
          The dir where the vanity keys are saved
  -d, --device <DEVICE>
          Device ID to use
  -t, --thread <THREAD>
          Adjust it to maximum your device's usage
  -i, --iteration <ITERATION>
          Adjust it to maximum your device's usage [default: 512]
      --timeout <TIMEOUT>
          Exit after a specified time in seconds
      --oneshot
          Exit after getting a vanity key
      --no-progress
          Don't print progress
      --no-secret-key-logging
          Don't print armored secret key
      --list-device
          Show available OpenCL devices then exit
      --future-timestamp
          Generate keys with future timestamps instead of past timestamps
          When true: search from start_timestamp forward in time (start_timestamp + 0 to max_time_range)
          When false: search from start_timestamp backward in time (start_timestamp - max_time_range to start_timestamp - 0)
      --start-timestamp <START_TIMESTAMP>
          Custom timestamp to start searching from (Unix timestamp)
          This is the base time point from which the search begins
          If not specified, uses current time as the starting point
          Example: 1640995200 (Jan 1, 2022 00:00:00 UTC)
      --max-time-range <MAX_TIME_RANGE>
          Maximum time range to search in seconds
          future_timestamp=true: search from start_timestamp to (start_timestamp + max_time_range)
          future_timestamp=false: search from (start_timestamp - max_time_range) to start_timestamp [default: 86400000]
  -h, --help
          Print help
  -V, --version
          Print version

$ opencl_vanity_gpg -p 11XXYYZZ --oneshot
[2025-01-08T19:00:25Z INFO  opencl_vanity_gpg] Using device: Apple M1 Pro
[2025-01-08T19:00:25Z INFO  opencl_vanity_gpg] Auto set thread: 1048576
[2025-01-08T19:00:25Z INFO  opencl_vanity_gpg] You will get vanity keys created after 2008-01-05T00:11:53.021Z
[2025-01-08T19:00:25Z WARN  opencl_vanity_gpg] No output dir given. Generated vanity keys will not be saved.
[2025-01-08T19:00:26Z INFO  opencl_vanity_gpg::utils::vanity_key] Get a vanity key:
-----BEGIN PGP PRIVATE KEY BLOCK-----

xVgER4EupBYJKwYBBAHaRw8BAQdAI4vIy0CaErtwj1iAQInMQYwIz4BMo30MfS1s
Kg0FYMUAAP4oOaeAXKE3fHhq1H28qYI+j7awA2iYQW7+fgTODpyXWxAfzRlEdW1t
eSA8ZHVtbXlAZXhhbXBsZS5jb20+wo4EEBYIADYCGQEFAmd+y0oCGwMECwkIBwUV
CgkICwUWAgMBAAEnFiEEucj6sO6iKUnbGDpx5F4DcRHMZiIACgkQ5F4DcRHMZiJ0
iQD/cUPO7lBsDbg5wyFwXalTvzcac8865OakjsdmA+bJPc8A/insYTxgzA/boh7i
ieogUSu64E0VyYGnfjcnIMX33mQPx10ER4EupBIKKwYBBAGXVQEFAQEHQPHXTpFg
T6dZ/eudJ0W+JzzfuzK8cCWlDcaWD/DEogVRAwEIBwAA/2I4tvG84tjPcZGxClnJ
nUpTRDrLvKtelZ5QBZLJbNJoEjXCeAQYFggAIAUCZ37LSgIbDBYhBLnI+rDuoilJ
2xg6ceReA3ERzGYiAAoJEOReA3ERzGYi8QwBAPr0n0eGhbNt5PMUfDccx4ttthFm
xsCkD3wdoVaA7t/BAQCvPyuVmtJN4M8gsYNRZYEfLwb1BIckohZv+svENGSqAw==
=ZeYm
-----END PGP PRIVATE KEY BLOCK-----

[2025-01-08T19:00:26Z INFO  opencl_vanity_gpg::utils::vanity_key] Created at: 2008-01-06T19:40:20.000Z (1199648420)
[2025-01-08T19:00:26Z INFO  opencl_vanity_gpg::utils::vanity_key] Fingerprint #0: B9C8FAB0EEA22949DB183A71E45E037111CC6622
[2025-01-08T19:00:26Z INFO  opencl_vanity_gpg::utils::vanity_key] Fingerprint #1: 7FBC6D063D9C4CF4C281E8A14876C8831552E9B4
[2025-01-08T19:00:26Z INFO  opencl_vanity_gpg] Hashed: 536.87M (512.00x) Time: 1.53s Speed: 351.76M hash/s
```

一个 Curve25519 的密钥由用来签名和认证的 Ed25519 主密钥和用来加密的 Cv25519 子密钥组成。VanityGPG [只能生成主密钥为“靓号”的密钥](https://github.com/RedL0tus/VanityGPG/issues/5)，而这个项目也可以生成子密钥为“靓号”的密钥（只需要添加参数 `-c cv25519` 即可）。对于其他 NISP P-\*\*\* 的椭圆曲线的密钥也是类似的。

# 性能对比

| Repo | 计算方式 | 速度（hash/s） | 注释 |
| - | - | - | - |
| [RedL0tus/VanityGPG](https://github.com/RedL0tus/VanityGPG) | CPU | 165m | Xeon w5-2465X ×16 cores <br> Arch Linux |
| 这个项目 | CPU | 120m | Xeon w5-2465X ×16 cores <br> Arch Linux <br> CPU 也可以是 OpenCL 的计算设备，虽然性能损耗比较严重…… |
| [cuihaoleo/gpg-fingerprint-filter-gpu](https://github.com/cuihaoleo/gpg-fingerprint-filter-gpu) | GPU | 1b | A16 1/8 <br> Ubuntu 24.04 |
| 这个项目 | GPU | 1.5b | A16 1/8 <br> Ubuntu 24.04 |
| [TransparentLC/webgl-vanity-gpg](https://github.com/TransparentLC/webgl-vanity-gpg) | GPU | 2b | GTX 1070 <br> Windows 11 |
| 这个项目 | GPU | 3b | GTX 1070 <br> Windows 11 |
| [TransparentLC/webgl-vanity-gpg](https://github.com/TransparentLC/webgl-vanity-gpg) | GPU | 7b | RTX A5500 <br> Windows 11 |
| 这个项目 | GPU | 12b | RTX A5500 <br> Windows 11 |
| 这个项目 | GPU | 32b | RTX 4090 <br> Ubuntu 22.04 |
| 这个项目 | GPU | 240m | RTX 4090 <br> Ubuntu 22.04 rsa4096 |
| 这个项目 | GPU | 42b | RTX 5090 <br> Windows 11 |
| 这个项目 | GPU | 380m | Apple M1 Pro |
| 这个项目 | GPU | 1.6b | Apple M4 Pro |

除另有标注外，以上的速度均为生成 cv25519 类型的密钥的速度。
