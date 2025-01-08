use std::str::FromStr;

use anyhow::bail;

#[derive(Debug, Clone)]
pub struct HashPattern {
    pub filter: String,
    pub possibliity: f64,
}

impl FromStr for HashPattern {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let pattern = match s.trim().replace(" ", "").to_ascii_uppercase() {
            x if x.len() <= 40 => "*".repeat(40 - x.len()) + &x,
            _ => bail!("Invalid pattern: {}", s),
        };
        let mut parts: Vec<String> = vec![];

        // Handle fixed 0-9A-F
        let mut fixed_pos_count: usize = 0;
        for i in 0..=4 {
            let mut mask = String::new();
            let mut value = String::new();
            let mut activated = false;
            for j in 0..8 {
                let char = *pattern.chars().nth(i * 8 + j).get_or_insert(' ');
                if char.is_ascii_hexdigit() {
                    fixed_pos_count += 1;
                    mask += "F";
                    value += &String::from(char);
                    activated = true;
                } else {
                    mask += "0";
                    value += "0";
                }
            }
            if activated {
                parts.push(format!("(h[{i}] & 0x{mask}) == 0x{value}"));
            }
        }

        // Handle wildcard G-Z
        let mut wildcard_pos_all: [Vec<usize>; (b'Z' - b'G' + 1) as usize] =
            std::default::Default::default();
        for (i, wildcard) in pattern.chars().enumerate() {
            if ('G'..='Z').contains(&wildcard) {
                wildcard_pos_all[((wildcard as u8) - b'G') as usize].push(i);
            }
        }
        let mut wildcard_pos_count = 0;

        for wildcard in 'G'..='Z' {
            let wildcard_pos = &wildcard_pos_all[((wildcard as u8) - b'G') as usize];
            if wildcard_pos.len() >= 2 {
                for i in 1..wildcard_pos.len() {
                    let left_index = wildcard_pos[i - 1] / 8;
                    let right_index = wildcard_pos[i] / 8;
                    let left_digit = 7 - wildcard_pos[i - 1] % 8;
                    let right_digit = 7 - wildcard_pos[i] % 8;
                    parts.push(format!(
                        "(/* {}: h[{}][{}] == h[{}][{}] */ (h[{}] {} {}) & 0xF{}) == (h[{}] & 0xF{})",
                        wildcard,
                        left_index,
                        left_digit,
                        right_index,
                        right_digit,
                        left_index,
                        if right_digit > left_digit { "<<" } else { ">>" },
                        right_digit.abs_diff(left_digit) * 4,
                        "0".repeat(right_digit),
                        right_index,
                        "0".repeat(right_digit),
                    ));
                }
                wildcard_pos_count += wildcard_pos.len() - 1;
            }
        }

        let filter = if !parts.is_empty() {
            parts.join(" && ")
        } else {
            String::from("true")
        };

        Ok(HashPattern {
            filter,
            possibliity: (16f64).powi((fixed_pos_count + wildcard_pos_count) as i32),
        })
    }
}
