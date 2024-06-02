parse-size
==========

[![Crates.io](https://img.shields.io/crates/v/parse-size.svg)](https://crates.io/crates/parse-size)
[![docs.rs](https://docs.rs/parse-size/badge.svg)](https://docs.rs/parse-size)
[![Build status](https://github.com/kennytm/parse-size/workflows/Rust/badge.svg)](https://github.com/kennytm/parse-size/actions?query=workflow%3ARust)
[![MIT License](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE.txt)

`parse-size` is an accurate, customizable, allocation-free library for
parsing byte size into integer.

```rust
use parse_size::parse_size;

assert_eq!(parse_size("0.2 MiB"), Ok(209715));
assert_eq!(parse_size("14.2e+8"), Ok(14_2000_0000));
```

## Features

* Supports both binary and decimal based prefix up to exabytes.
* Numbers can be fractional and/or in scientific notation. `parse-size` can accurately parse the input using the full 64-bit precision.
* The unit is case-insensitive. The "B" suffix is also optional (`1 KiB` = `1 kib` = `1Ki`).
* Fractional bytes are allowed, and rounded to nearest integer (`2.5 KiB` = `2560`, `2.5B` = `3`).
* Underscores and spaces in the numbers are ignored to support digit grouping (`123_456` = `123456`).
* Conventional units (KB, GB, ...) can be configured to use the binary system.
* `#![no_std]`-capable, no dependencies, and uses no heap allocation.
