# Well-known primes module

Implement a `well_known_prime` tactic that proves `IsPrime n` using
`decide` (with `native_decide` fallback for large primes) via a two-tier
strategy: first an O(1) HashSet lookup
against precomputed elliptic curve prime sets (Curve25519, secp256k1,
NIST P-256/384, Ed448-Goldilocks, E-521, etc.), then a deterministic
Miller-Rabin fallback for primes not in the sets.

- Primality.lean: modular exponentiation, Miller-Rabin witness test
  using 25 prime witnesses (correct for all n < 3.317e24)
- Data.lean: HashSets of known primes from 20 elliptic curve families
- Tactic.lean: combined isPrime (HashSet fast path + Miller-Rabin),
  IsPrime proposition, and the well_known_prime tactic