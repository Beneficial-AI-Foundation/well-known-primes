/-
  Deterministic Miller-Rabin primality test and IsPrime proposition.

  The `isPrime` function uses 25 prime witnesses, which is provably correct
  for all n < 3.317 × 10²⁴. No known composite passes all 25 witnesses.
-/

namespace WellKnownPrime

/-- Modular exponentiation: `modPow base exp mod` computes `base ^ exp % mod`.
    Uses binary method (repeated squaring) with accumulator for tail recursion. -/
def modPow (base exp mod : Nat) : Nat :=
  if mod ≤ 1 then 0
  else loop (base % mod) exp 1 mod
where
  loop (base exp acc mod : Nat) : Nat :=
    if h : exp = 0 then acc
    else
      let acc := if exp % 2 = 1 then acc * base % mod else acc
      loop (base * base % mod) (exp / 2) acc mod
  termination_by exp
  decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Factor out powers of 2: returns `(d, r)` where `n = d * 2^r` and `d` is odd. -/
def factorPowersOf2 (n : Nat) : Nat × Nat :=
  go n 0
where
  go (d r : Nat) : Nat × Nat :=
    if h : d > 0 ∧ d % 2 = 0 then
      go (d / 2) (r + 1)
    else
      (d, r)
  termination_by d
  decreasing_by exact Nat.div_lt_self h.1 (by omega)

/-- Inner loop of Miller-Rabin witness test. Repeatedly squares `x` mod `n`,
    checking if we reach `n - 1`. -/
private def millerRabinLoop (n nm1 : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | count + 1, x =>
    let x := x * x % n
    if x = nm1 then true
    else millerRabinLoop n nm1 count x

/-- Miller-Rabin single witness test. Returns `true` if `n` passes with witness `a`.
    `d` and `r` satisfy `n - 1 = d * 2^r` with `d` odd. -/
def millerRabinWitness (n a d r : Nat) : Bool :=
  let x := modPow a d n
  if x = 1 || x = n - 1 then true
  else millerRabinLoop n (n - 1) (r - 1) x

/-- Deterministic Miller-Rabin witnesses (first 25 primes).
    Provably correct for all n < 3,317,044,064,679,887,385,961,981.
    No known composite passes all witnesses for any n. -/
private def witnesses : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
   53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

/-- Deterministic primality test using Miller-Rabin. -/
def millerRabinIsPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n < 4 then true
  else if n % 2 = 0 then false
  else if n % 3 = 0 then false
  else
    let (d, r) := factorPowersOf2 (n - 1)
    witnesses.all fun a =>
      if a ≥ n then true
      else millerRabinWitness n a d r

end WellKnownPrime
