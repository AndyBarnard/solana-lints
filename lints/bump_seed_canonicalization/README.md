# bump_seed_canonicalization

**What it does:**
Finds uses of solana_program::pubkey::PubKey::create_program_address that do not check the bump_seed

**Why is this bad?**
Generally for every seed there should be a canonical address.

**Known problems:**
False positives, since the bump_seed check may be within some other function (does not
trace through function calls)
False negatives, since our analysis is not path-sensitive (the bump_seed check may not
occur in all possible execution paths)

\**Example:*j

```rust
// example code where a warning is issued

```

Use instead:

```rust

```
