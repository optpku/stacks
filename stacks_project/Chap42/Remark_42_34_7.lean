/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.OneRing

/-!
# Remark 42.34.7: completed cutoff products, with an explicit local erratum

The original arbitrary-cutoff algebra and `max p q` claim is false: the zero
section of `P³ × A¹` with cutoff two violates associativity for every proposed
ambient-to-relative crossing product. The recorded local correction retains
the integer-degree completed carrier and the three bivariant pairings, defines
the canonical product into cutoff `p + q`, and states its associativity with
addition of cutoff parameters. Low degrees use actual proper pushforward.
The genuine fixed-cutoff-one convolution ring is a separate assertion.

Original source is preserved. The counterexample, authorisation and exact
before/after scope are recorded in local-error-records/0FA0; no extra geometric
assumptions, arbitrary maps or opaque existence-based data are introduced.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.BivariantClass

universe u

section

variable {S : Scheme.{u}} [UniversallyCatenary S]
  (δ : S → ℤ) [IsDimensionFunction δ]
  {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
  (f : Z ⟶ X) [IsClosedImmersion f.left]

/- Remark 42.34.7 (1): the degreewise cutoff family `A⁽ᵖ⁾(Z ⟶ X)`. -/
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff

/- Remark 42.34.7 (2): multiplication of a relative class by an ambient class. -/
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.relativeMulAmbient
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.relativeMulAmbient_apply

/- Remark 42.34.7 (3): multiplication of an ambient class by a relative class. -/
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.ambientMulRelative
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.ambientMulRelative_apply

/- Remark 42.34.7 (4): multiplication of two relative classes. -/
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.relativeMul
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.relativeMul_apply

/- Remark 42.34.7 (5): the full original integer-indexed completed carrier. -/
@[stacks 0FA0] #check
  (Cutoff.Completed δ f : ℕ → Type (u + 1))

/- Remark 42.34.7 (6): every integer degree retains the original ambient/relative branch. -/
@[stacks 0FA0] #check
  (Cutoff.completed_def δ f : ∀ p : ℕ, Cutoff.Completed δ f p = ∀ n : ℤ,
    if n < (p : ℤ) then ChowCohomology.degree δ X.hom n else BivariantClass δ f n)

/- Remark 42.34.7 (7): local erratum, actual homogeneous sum-cutoff multiplication. -/
@[stacks 0FA0] #check
  (Cutoff.degreeMul δ f : ∀ p q : ℕ, ∀ {i j : ℤ},
    Cutoff δ f p i → Cutoff δ f q j → Cutoff δ f (p + q) (i + j))

/- Remark 42.34.7 (8): local erratum, actual completed product into cutoff p + q. -/
@[stacks 0FA0] #check
  (Cutoff.completedMul δ f : ∀ p q : ℕ,
    Cutoff.Completed δ f p → Cutoff.Completed δ f q → Cutoff.Completed δ f (p + q))

/- Remark 42.34.7 (9): local erratum, associativity for the specified completed map. -/
@[stacks 0FA0] #check
  (Cutoff.completedMul_assoc δ f : ∀ (p q r : ℕ)
    (a : Cutoff.Completed δ f p) (b : Cutoff.Completed δ f q)
    (c : Cutoff.Completed δ f r),
    Cutoff.castCompleted δ f (Nat.add_assoc p q r)
        (Cutoff.completedMul δ f (p + q) r (Cutoff.completedMul δ f p q a b) c) =
      Cutoff.completedMul δ f p (q + r) a (Cutoff.completedMul δ f q r b c))

/- Remark 42.34.7 (10): bilinearity in the first completed input. -/
@[stacks 0FA0] #check
  (Cutoff.completedMul_add_left δ f : ∀ (p q : ℕ)
    (a a' : Cutoff.Completed δ f p) (b : Cutoff.Completed δ f q),
    Cutoff.completedMul δ f p q (a + a') b =
      Cutoff.completedMul δ f p q a b + Cutoff.completedMul δ f p q a' b)

/- Remark 42.34.7 (11): bilinearity in the second completed input. -/
@[stacks 0FA0] #check
  (Cutoff.completedMul_add_right δ f : ∀ (p q : ℕ)
    (a : Cutoff.Completed δ f p) (b b' : Cutoff.Completed δ f q),
    Cutoff.completedMul δ f p q a (b + b') =
      Cutoff.completedMul δ f p q a b + Cutoff.completedMul δ f p q a b')

/- Remark 42.34.7 (12): local erratum, the independent fixed-cutoff-one ring. -/
@[stacks 0FA0] #check
  (Cutoff.completedRingOne δ f : Ring (Cutoff.Completed δ f 1))

/- Negative-degree vanishing justifies the explicit finite-convolution model;
it is a conclusion in the original scope, not a new input hypothesis. -/
#check (Cutoff.eq_zero_of_negative δ f : ∀ (p : ℕ) (n : ℤ),
  n < 0 → ∀ c : Cutoff δ f p n, c = 0)
#check (Cutoff.completedEquivFamily δ f : ∀ p : ℕ,
  Cutoff.Completed δ f p ≃+ Cutoff.Family δ f p)

end
