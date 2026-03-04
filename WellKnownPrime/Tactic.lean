/-
  The `well_known_prime` tactic for proving `IsPrime n` goals.

  Uses a two-tier strategy:
  1. Fast O(1) HashSet lookup against known elliptic curve primes
  2. Falls back to deterministic Miller-Rabin for primes not in the sets

  Both paths are compiled to native code via `native_decide`.
-/

import WellKnownPrime.Primality
import WellKnownPrime.Data
import Lean.Elab.Tactic

namespace WellKnownPrime

/-- Combined primality test: checks the known elliptic curve prime HashSets
    first (O(1) lookup), then falls back to Miller-Rabin. -/
def isPrime (n : Nat) : Bool :=
  well_known_prime n || millerRabinIsPrime n

/-- `IsPrime n` holds when `isPrime` confirms `n` is prime. -/
def IsPrime (n : Nat) : Prop := isPrime n = true

instance (n : Nat) : Decidable (IsPrime n) :=
  inferInstanceAs (Decidable (isPrime n = true))

open Lean Elab Tactic

/-- `well_known_prime` proves goals of the form `WellKnownPrime.IsPrime n`
    by evaluating the combined primality test via native code execution.

    For known elliptic curve primes, this is an O(1) HashSet lookup.
    For other primes, it falls back to deterministic Miller-Rabin.

    ```
    example : WellKnownPrime.IsPrime 104729 := by well_known_prime
    ```
-/
elab "well_known_prime" : tactic => do
  try
    evalTactic (← `(tactic| native_decide))
  catch _ =>
    evalTactic (← `(tactic| decide +native))

end WellKnownPrime
