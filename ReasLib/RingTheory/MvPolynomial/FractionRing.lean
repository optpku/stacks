/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fraction rings under multivariate coefficient base change

This leaf owns the canonical comparison between the fraction ring of a
multivariate polynomial ring and the fraction ring after extending
coefficients to a chosen fraction-field model.  It is indexed by an arbitrary
variable type, rather than by a presentation-specific finite index.
-/

@[expose] public section

universe u v w

namespace MvPolynomial.FractionRing

variable {σ : Type u} {R : Type v} {K : Type w}
variable [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

-- Mathlib deliberately keeps this lift out of global typeclass search to avoid algebra diamonds.
attribute [local instance] _root_.FractionRing.liftAlgebra _root_.FractionRing.isScalarTower_liftAlgebra

/-- The chosen fraction-field model maps into the fraction ring of a
multivariate polynomial ring through coefficient constants. -/
noncomputable def coefficientLift :
    K →+* _root_.FractionRing (MvPolynomial σ R) :=
  IsFractionRing.lift
    (K := K) (L := _root_.FractionRing (MvPolynomial σ R))
    (g := algebraMap R (_root_.FractionRing (MvPolynomial σ R)))
    (FaithfulSMul.algebraMap_injective R (_root_.FractionRing (MvPolynomial σ R)))

/-- The coefficient-extension polynomial map into the original rational
function field.  It sends variables to their canonical rational functions. -/
noncomputable def baseChangeBackward :
    MvPolynomial σ K →+* _root_.FractionRing (MvPolynomial σ R) :=
  MvPolynomial.eval₂Hom coefficientLift
    (fun i ↦
      algebraMap (MvPolynomial σ R) (_root_.FractionRing (MvPolynomial σ R))
        (MvPolynomial.X i))

/-- The fraction-field map induced by extending polynomial coefficients from
`R` to its chosen fraction-field model `K`. -/
noncomputable def baseChangeForward :
    _root_.FractionRing (MvPolynomial σ R) →+*
      _root_.FractionRing (MvPolynomial σ K) :=
  IsFractionRing.map
    (K := _root_.FractionRing (MvPolynomial σ R))
    (L := _root_.FractionRing (MvPolynomial σ K))
    (j := MvPolynomial.map (algebraMap R K))
    (MvPolynomial.map_injective (σ := σ) (f := algebraMap R K)
      (IsFractionRing.injective R K))

/-- The backward coefficient-extension polynomial map is injective. -/
theorem baseChangeBackward_injective :
    Function.Injective (baseChangeBackward (σ := σ) (R := R) (K := K)) := sorry

/-- The inverse fraction-field map induced by the backward polynomial map. -/
noncomputable def baseChangeInverse :
    _root_.FractionRing (MvPolynomial σ K) →+*
      _root_.FractionRing (MvPolynomial σ R) :=
  IsFractionRing.map
    (K := _root_.FractionRing (MvPolynomial σ K))
    (L := _root_.FractionRing (MvPolynomial σ R))
    (j := baseChangeBackward (σ := σ) (R := R) (K := K))
    (baseChangeBackward_injective (σ := σ) (R := R) (K := K))

/-- The inverse fraction-field map is a left inverse to coefficient base
change. -/
theorem baseChangeInverse_comp_forward :
    (baseChangeInverse (σ := σ) (R := R) (K := K)).comp
        (baseChangeForward (σ := σ) (R := R) (K := K)) =
      RingHom.id (_root_.FractionRing (MvPolynomial σ R)) := sorry

/-- The inverse fraction-field map is a right inverse to coefficient base
change. -/
theorem baseChangeForward_comp_inverse :
    (baseChangeForward (σ := σ) (R := R) (K := K)).comp
        (baseChangeInverse (σ := σ) (R := R) (K := K)) =
      RingHom.id (_root_.FractionRing (MvPolynomial σ K)) := sorry

/-- The forward fraction-field map respects the original `R`-algebra
structures. -/
theorem baseChangeForward_commutes (r : R) :
    baseChangeForward (σ := σ) (R := R) (K := K)
        (algebraMap R (_root_.FractionRing (MvPolynomial σ R)) r) =
      algebraMap R (_root_.FractionRing (MvPolynomial σ K)) r := sorry

/-- The concrete ring equivalence induced by coefficient base change to a
fraction-field model. -/
noncomputable def baseChangeRingEquiv :
    _root_.FractionRing (MvPolynomial σ R) ≃+*
      _root_.FractionRing (MvPolynomial σ K) :=
  RingEquiv.ofRingHom
    (baseChangeForward (σ := σ) (R := R) (K := K))
    (baseChangeInverse (σ := σ) (R := R) (K := K))
    (baseChangeForward_comp_inverse (σ := σ) (R := R) (K := K))
    (baseChangeInverse_comp_forward (σ := σ) (R := R) (K := K))

/-- Tag `00PH`: extending coefficients of a multivariate polynomial ring to a
chosen fraction-field model does not change its fraction field.  This is the
canonical reusable comparison for arbitrary variable type `σ`. -/
@[stacks 00PH "multivariate polynomial fraction-field base change"]
noncomputable def baseChangeAlgEquiv :
    _root_.FractionRing (MvPolynomial σ R) ≃ₐ[R]
      _root_.FractionRing (MvPolynomial σ K) :=
  AlgEquiv.ofRingEquiv
    (f := baseChangeRingEquiv (σ := σ) (R := R) (K := K))
    (baseChangeForward_commutes (σ := σ) (R := R) (K := K))

/-- The canonical coefficient-base-change equivalence agrees with the
localized polynomial coefficient map on polynomial numerators. -/
@[simp, stacks 00PH "multivariate fraction-field base change on numerators"]
theorem baseChangeAlgEquiv_algebraMap (p : MvPolynomial σ R) :
    baseChangeAlgEquiv (σ := σ) (R := R) (K := K)
        (algebraMap (MvPolynomial σ R) (_root_.FractionRing (MvPolynomial σ R)) p) =
      algebraMap (MvPolynomial σ K) (_root_.FractionRing (MvPolynomial σ K))
        (MvPolynomial.map (algebraMap R K) p) := sorry

end MvPolynomial.FractionRing
