module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quotients of adic completions

This file owns the canonical map from a `J`-adic completion to a quotient
`R ⧸ I` whenever a power of `J` is contained in `I`.  The construction is
independent of divided powers and of any primality hypothesis.
-/

noncomputable section

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- The canonical map from the `J`-adic completion of `R` to `R ⧸ I`, evaluated at any
stage `n` for which `J ^ n ≤ I`. -/
@[stacks 07KD "completion-to-quotient map"]
noncomputable def toQuotient (J I : Ideal R) (n : ℕ) (h : J ^ n ≤ I) :
    AdicCompletion J R →+* R ⧸ I :=
  (Ideal.Quotient.factor h).comp (AdicCompletion.evalₐ J n).toRingHom

/-- The map `toQuotient` extends the quotient map on `R`. -/
theorem toQuotient_comp_algebraMap (J I : Ideal R) (n : ℕ) (h : J ^ n ≤ I) :
    (toQuotient J I n h).comp (algebraMap R (AdicCompletion J R)) =
      Ideal.Quotient.mk I := sorry

/-- A quotient killed by a power of the defining ideal is also a
quotient of the adic completion. -/
@[stacks 07KD "adic completion maps onto a quotient killed by an ideal power"]
theorem toQuotient_surjective (J I : Ideal R) (n : ℕ) (h : J ^ n ≤ I) :
    Function.Surjective (toQuotient J I n h) := sorry

namespace Principal

/-- For a principal adic topology, the kernel of the map to
`R ⧸ I` is the image of the completion of `I` inside the completion of `R`. -/
@[stacks 07KD "kernel of a principal-adic completion quotient map"]
theorem mem_ker_toQuotient_iff (r : R) (I : Ideal R) (n : ℕ)
    (h : Ideal.span {r} ^ n ≤ I) {x : AdicCompletion (Ideal.span {r}) R} :
    x ∈ RingHom.ker (toQuotient (Ideal.span {r}) I n h) ↔
      ∃ y : AdicCompletion (Ideal.span {r}) I,
        AdicCompletion.map (Ideal.span {r}) I.subtype y = x := sorry

end Principal

end AdicCompletion
