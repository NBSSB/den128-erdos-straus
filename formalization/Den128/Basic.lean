/-!
Den128.Basic

Core definitions for the denominator-128 family of the Erdős--Straus problem.

Family: x = 2^7 * 3^b, d = 128 + 3^k, p = 2^9 * 3^b - (128 + 3^k)
with 0 ≤ k ≤ b.

All proofs are complete -- no sorry or admit placeholders.
-/

namespace Den128

/-- Natural-number parameters for the denominator-128 family. -/
structure Params where
  b : Nat
  k : Nat
  support : k ≤ b
deriving Repr, DecidableEq

namespace Params

/-- The family value x = 2^7 * 3^b. -/
def x (P : Params) : Nat :=
  2^7 * 3^P.b

/-- The denominator-side offset d = 128 + 3^k. -/
def d (P : Params) : Nat :=
  128 + 3^P.k

/--
The prime-gate integer p = 2^9 * 3^b - (128 + 3^k).

We work in Int to avoid hidden truncating Nat subtraction.
The value is positive for all b ≥ 3, k ≤ b.
-/
def pInt (P : Params) : Int :=
  (2^9 : Int) * (3^P.b : Int) - ((128 : Int) + (3^P.k : Int))

/-- Nat version of p (for primality testing). -/
def pNat (P : Params) : Nat :=
  (2^9) * (3^P.b) - (128 + 3^P.k)

end Params

/-- Support predicate: k ≤ b. -/
def Support (P : Params) : Prop :=
  P.k ≤ P.b

/--
Exactness predicate for the denominator-128 family.

A row is exact if 3^k ≡ -128 (mod d), which holds by construction
since d = 128 + 3^k.
-/
def ExactDen128 (P : Params) : Prop :=
  (3^P.k + 128) % P.d = 0

/--
Prime-gate branch predicate.

A row enters the prime Erdős--Straus branch if pNat is prime.
-/
def PrimeGateBranch (P : Params) : Prop :=
  Nat.Prime P.pNat

/--
Congruence condition for prime q dividing p.

q ∣ p iff 2^9 * 3^b ≡ 128 + 3^k (mod q).
-/
def qDivides (q : Nat) (P : Params) : Prop :=
  ((2^9 * 3^P.b) % q) = ((128 + 3^P.k) % q)

/--
Carrier model boundary: pInt equals the stated formula.

Proof: definitional equality (rfl).
-/
theorem carrier_model_boundary (P : Params) :
    P.pInt = (2^9 : Int) * (3^P.b : Int) - ((128 : Int) + (3^P.k : Int)) := by
  rfl

/--
Support visibility: every Params satisfies k ≤ b by construction.

Proof: direct from structure field.
-/
theorem support_visible (P : Params) : Support P :=
  P.support

end Den128
