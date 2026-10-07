module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.LocalEquiv
public import ReasLib.RingTheory.LocalRing.Equiv.MaximalIdeal

@[expose] public section

/-!
# Finite stages of maximal-ideal completion equivalences

@stack 0CAR

The ring-level quotient-stage comparison is owned by
`RingEquiv.MaximalIdeal`.  This leaf only records its compatibility with the
canonical maps out of maximal-ideal adic completions.
-/

open IsLocalRing

namespace AdicCompletion.LocalEquiv

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]

/-- Evaluating a maximal-ideal completion equivalence at a finite stage gives the corresponding
maximal-ideal quotient-power equivalence. -/
@[stacks 0CAR "finite-stage naturality of a maximal-ideal completion equivalence"]
theorem evalₐ_comp_mapLocalEquiv (e : A ≃+* B) (n : ℕ) :
    (AdicCompletion.evalₐ (maximalIdeal B) n).toRingHom.comp
        (AdicCompletion.mapLocalEquiv e).toRingHom =
      (RingEquiv.MaximalIdeal.quotientPowEquiv e n).toRingHom.comp
        (AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom := sorry

/-- The pointwise finite-stage evaluation formula for `AdicCompletion.mapLocalEquiv`. -/
@[stacks 0CAR "pointwise finite-stage naturality of a completion equivalence"]
theorem evalₐ_mapLocalEquiv (e : A ≃+* B) (n : ℕ)
    (x : AdicCompletion (maximalIdeal A) A) :
    AdicCompletion.evalₐ (maximalIdeal B) n (AdicCompletion.mapLocalEquiv e x) =
      RingEquiv.MaximalIdeal.quotientPowEquiv e n
        (AdicCompletion.evalₐ (maximalIdeal A) n x) := sorry

/-- Evaluating the inverse maximal-ideal completion equivalence at a finite stage gives the
inverse quotient-power equivalence. -/
@[stacks 0CAR "inverse finite-stage naturality of a completion equivalence"]
theorem evalₐ_comp_mapLocalEquiv_symm (e : A ≃+* B) (n : ℕ) :
    (AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom.comp
        (AdicCompletion.mapLocalEquiv e).symm.toRingHom =
      (RingEquiv.MaximalIdeal.quotientPowEquiv e n).symm.toRingHom.comp
        (AdicCompletion.evalₐ (maximalIdeal B) n).toRingHom := sorry

/-- The pointwise finite-stage evaluation formula for the inverse of
`AdicCompletion.mapLocalEquiv`. -/
@[stacks 0CAR "pointwise inverse finite-stage naturality of a completion equivalence"]
theorem evalₐ_mapLocalEquiv_symm (e : A ≃+* B) (n : ℕ)
    (x : AdicCompletion (maximalIdeal B) B) :
    AdicCompletion.evalₐ (maximalIdeal A) n ((AdicCompletion.mapLocalEquiv e).symm x) =
      (RingEquiv.MaximalIdeal.quotientPowEquiv e n).symm
        (AdicCompletion.evalₐ (maximalIdeal B) n x) := sorry

end AdicCompletion.LocalEquiv
