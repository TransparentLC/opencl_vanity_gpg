# opencl_vanity_gpg

使用 GPU（OpenCL）快速生成带有“靓号”的 PGP 密钥！

“靓号”指的是带有连号等特定格式的密钥指纹或 ID（例如以 `77777777` 结尾），具体介绍和生成原理请参见：

* [一位 PGP 进步青年的科学算号实践](https://www.douban.com/note/763978955/)
* [某科学的 PGP 算号指南](https://blog.dejavu.moe/posts/the-scientific-vanity-pgp-counting-guide/)

![](https://github.com/user-attachments/assets/e6364d93-fffe-4fcd-9857-b70155e6f476)

简单来说，密钥指纹是密钥生效时间和公钥内容的 SHA-1，通过不断生成密钥和修改时间（成本更低）的暴力遍历方式找到“靓号”。

> [!TIP]
>
> 姊妹项目：使用 WebGL 实现的网页版 [TransparentLC/webgl-vanity-gpg](https://github.com/TransparentLC/webgl-vanity-gpg)
>
> 实际上这个项目也可以当成是它的“锈化”版…\_φ(･ω･` )

目前最好的同类工具是使用 CPU 的 [RedL0tus/VanityGPG](https://github.com/RedL0tus/VanityGPG) 和使用 GPU（CUDA）的 [cuihaoleo/gpg-fingerprint-filter-gpu](https://github.com/cuihaoleo/gpg-fingerprint-filter-gpu)。这个项目是使用 GPU（OpenCL）实现的，优点当然是开箱即用了。

GitHub Actions 有自动编译好的二进制文件。

# 使用方法

```console
$ opencl_vanity_gpg -h
Usage: opencl_vanity_gpg [OPTIONS]

Options:
  -c, --cipher-suite <CIPHER_SUITE>  Cipher suite of the vanity key
                                     ed25519, ecdsa-****, rsa**** => Primary key
                                     cv25519,  ecdh-****          => Subkey
                                     Use gpg CLI for further editing of the key. [default: ed25519] [possible values: ed25519, cv25519, rsa2048, rsa3072, rsa4096, ecdh-p256, ecdh-p384, ecdh-p521, ecdsa-p256, ecdsa-p384, ecdsa-p521]
  -u, --user-id <USER_ID>            OpenPGP compatible user ID [default: "Dummy <dummy@example.com>"]
  -p, --pattern <PATTERN>            A pattern less than 40 chars for matching fingerprints
                                     Format:
                                     * 0-9A-F are fixed, G-Z are wildcards
                                     * Other chars will be ignored
                                     * Case insensitive
                                     Example:
                                     * 11XXXX** may output a fingerprint ends with 11222234 or 11AAAABF
                                     * 11XXYYZZ may output a fingerprint ends with 11223344 or 11AABBCC
  -f, --filter <FILTER>              OpenCL kernel function for uint h[5] for matching fingerprints
                                     Ignore the pattern and no estimate is given if this has been set
                                     Example:
                                     * (h[4] & 0xFFFF)     == 0x1234     outputs a fingerprint ends with 1234
                                     * (h[0] & 0xFFFF0000) == 0xABCD0000 outputs a fingerprint starts with ABCD
  -o, --output <OUTPUT>              The dir where the vanity keys are saved
  -d, --device <DEVICE>              Device ID to use
  -t, --thread <THREAD>              Adjust it to maximum your device's usage
  -i, --iteration <ITERATION>        Adjust it to maximum your device's usage [default: 512]
      --timeout <TIMEOUT>            Exit after a specified time in seconds
      --oneshot                      Exit after getting a vanity key
      --no-progress                  Don't print progress
      --no-secret-key-logging        Don't print armored secret key
      --device-list                  Show available OpenCL devices then exit
  -h, --help                         Print help
  -V, --version                      Print version

$ opencl_vanity_gpg -p 111XXXYYYZZZ --oneshot
[2025-01-08T13:50:49Z INFO  opencl_vanity_gpg] Using device: NVIDIA GeForce GTX 1070
[2025-01-08T13:50:49Z INFO  opencl_vanity_gpg] Auto set thread: 1048576
[2025-01-08T13:50:49Z INFO  opencl_vanity_gpg] You will get vanity keys created after 2008-01-04T19:02:17.598Z
[2025-01-08T13:50:49Z WARN  opencl_vanity_gpg] No output dir given. Generated vanity keys will not be saved.
[2025-01-08T13:50:58Z INFO  opencl_vanity_gpg] Get a vanity key:
-----BEGIN PGP PRIVATE KEY BLOCK-----

xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
xxxxx
-----END PGP PRIVATE KEY BLOCK-----

[2025-01-08T13:50:58Z INFO  opencl_vanity_gpg] Created at: 2022-10-07T18:07:54.000Z (1665166074)
[2025-01-08T13:50:58Z INFO  opencl_vanity_gpg] Fingerprint #0: 8A166AF156114C8847390E158CB2111000AAAEEE
[2025-01-08T13:50:58Z INFO  opencl_vanity_gpg] Fingerprint #1: AC6D0BE52B29AB00CFF4841CEDD530E847FD5DF6
[2025-01-08T13:50:58Z INFO  opencl_vanity_gpg] Hashed: 32749.13m (0.48x) Time: 8.71s Speed: 3761.64m hash/s
```

一个 Curve25519 的密钥由用来签名和认证的 Ed25519 主密钥和用来加密的 Cv25519 子密钥组成。VanityGPG [只能生成主密钥为“靓号”的密钥](https://github.com/RedL0tus/VanityGPG/issues/5)，而这个项目也可以生成子密钥为“靓号”的密钥（只需要添加参数 `-c cv25519` 即可）。对于其他 NISP P-*** 的椭圆曲线的密钥也是类似的。

# 性能对比

| Repo | 计算方式 | 速度（hash/s） | 注释 |
| - | - | - | - |
| [RedL0tus/VanityGPG](https://github.com/RedL0tus/VanityGPG) | CPU | 165m | Xeon w5-2465X ×16 cores |
| 这个项目 | CPU | 120m | Xeon w5-2465X ×16 cores <br> CPU 也可以是 OpenCL 的计算设备，虽然性能损耗比较严重…… |
| [TransparentLC/webgl-vanity-gpg](https://github.com/TransparentLC/webgl-vanity-gpg) | GPU | 2b | GTX 1070 |
| 这个项目 | GPU | 3b | GTX 1070 |
| [TransparentLC/webgl-vanity-gpg](https://github.com/TransparentLC/webgl-vanity-gpg) | GPU | 7b | RTX A5500 |
| 这个项目 | GPU | 12b | RTX A5500 |

以上的速度均为生成 Curve25519 类型的密钥的速度。
