import WellKnownPrime

open WellKnownPrime

-- Small primes
example : IsPrime 2 := by well_known_prime
example : IsPrime 17 := by well_known_prime
example : IsPrime 97 := by well_known_prime

-- Medium prime
example : IsPrime 104729 := by well_known_prime

-- Curve25519 field prime (78 digits)
example : IsPrime 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  well_known_prime

-- E-521 field prime (157 digits)
example : IsPrime 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 := by
  well_known_prime

def main : IO Unit := do
  -- Runtime primality checks
  IO.println s!"isPrime 561 (Carmichael) = {isPrime 561}"
  IO.println s!"isPrime 104729 = {isPrime 104729}"
  IO.println "All primality proofs checked."
