/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.ReesAlgebra.Grading

/-!
# Affine charts of Rees-algebra blowups

For an ideal `I` and an element `a : I`, this file defines the affine chart
obtained by homogeneous localization of `reesAlgebra I` at `a t`.  It keeps the
construction entirely ring-theoretic and supplies the comparison map to the
ordinary localization away from `a`.
-/

@[expose] public section

noncomputable section

universe u v

open HomogeneousLocalization
open scoped DirectSum

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

/-- For `a ∈ I`, the affine blowup chart
`R[I / a]` is the degree-zero homogeneous localization of `reesAlgebra I` at
the degree-one element `a t`. -/
@[stacks 052Q]
abbrev affineBlowupChart (a : I) :=
  Away (ReesAlgebra.Grading.grade I) (ReesAlgebra.Grading.degreeOne I a)

namespace AffineBlowupChart

/-! The scoped notation `R[I / a]` names `affineBlowupChart I a`. -/
scoped syntax:max term:max "[" term:max " / " term:max "]" : term

/-! Elaborate `R[I / a]` as the affine blowup chart associated to `a : I`. -/
scoped macro_rules (kind := AffineBlowupChart.«term_[_/_]»)
  | `($R[$I / $a]) => `(@affineBlowupChart $R _ $I $a)

/-- A center element together with the nonzero condition required for ordinary fraction maps. -/
@[stacks 052Q "affine blowup chart nonzero parameter"]
abbrev NonzeroParameter (J : Ideal R) := { a : J // (a : R) ≠ 0 }

end AffineBlowupChart

open scoped AffineBlowupChart

/-- The canonical map from `R` into the homogeneous-localization affine chart
`R[I / a]`. -/
@[stacks 052Q "affine blowup chart algebra map"]
protected noncomputable abbrev AffineBlowupChart.algebraMap (a : I) : R →+* R[I / a] :=
  (fromZeroRingHom (ReesAlgebra.Grading.grade I)
    (Submonoid.powers (ReesAlgebra.Grading.degreeOne I a))).comp
    (ReesAlgebra.Grading.zeroAlgebraMap I)

namespace AffineBlowupChart

/-- The canonical map from the base ring to an affine blowup chart has central image. -/
theorem algebraMap_commutes (a : I) (r : R) (x : R[I / a]) :
    AffineBlowupChart.algebraMap I a r * x =
      x * AffineBlowupChart.algebraMap I a r := sorry

/-- Scalar multiplication on an affine blowup chart is multiplication by the canonical image of
the scalar. -/
theorem algebraMap_smul_def (a : I) (r : R) (x : R[I / a]) :
    r • x = AffineBlowupChart.algebraMap I a r * x := sorry

/-- The affine blowup chart carries the `R`-algebra structure induced from its
degree-zero Rees piece. -/
@[stacks 052Q "affine blowup chart algebra"]
instance instAlgebra (a : I) : Algebra R R[I / a] :=
  { toSMul := HomogeneousLocalization.instSMul _
    algebraMap := AffineBlowupChart.algebraMap I a
    commutes' := algebraMap_commutes I a
    smul_def' := algebraMap_smul_def I a }

/-- An affine blowup chart over an algebra carries the composite algebra structure from every
lower scalar ring. -/
@[stacks 052Q "affine blowup chart scalar algebra"]
noncomputable instance (priority := 50) instAlgebraOfTower
    {A : Type v} [CommRing A] [Algebra A R] (a : I) : Algebra A R[I / a] :=
  Algebra.compHom R[I / a] (algebraMap A R)

/-- The canonical algebra structures on an affine blowup chart form a scalar tower. -/
@[stacks 052Q "affine blowup chart scalar tower"]
noncomputable instance instIsScalarTower
    {A : Type v} [CommRing A] [Algebra A R] (a : I) :
    IsScalarTower A R R[I / a] := sorry

end AffineBlowupChart

/-- The basic homogeneous fraction `x t / a t` in the affine blowup chart
`R[I / a]`. -/
@[stacks 052Q "affine blowup chart basic fraction"]
noncomputable def AffineBlowupChart.basicFraction (a x : I) : R[I / a] :=
  Away.mk (ReesAlgebra.Grading.grade I) (ReesAlgebra.Grading.degreeOne_mem I a) 1
    (ReesAlgebra.Grading.degreeOne I x) (ReesAlgebra.Grading.degreeOne_mem I x)

/-- The Rees monomial with coefficient in `I ^ n` lies in the degree required for a normalized
affine-chart fraction. -/
theorem AffineBlowupChart.powerFraction_numerator_mem
    (n : ℕ) (r : ↥(I ^ n)) :
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      ReesAlgebra.Grading.grade I (n • 1) := sorry

/-- The normalized degree-`n` fraction with numerator in `I ^ n` and denominator `a ^ n`.

This is the canonical monomial chart generator used by power filtrations and base-change
arguments.  It is deliberately defined from the graded localization rather than from a chosen
presentation of the ordinary localization. -/
@[stacks 052Q "affine blowup chart power fraction"]
noncomputable def AffineBlowupChart.powerFraction
    (a : I) (n : ℕ) (r : ↥(I ^ n)) : R[I / a] :=
  Away.mk (ReesAlgebra.Grading.grade I) (ReesAlgebra.Grading.degreeOne_mem I a) n
    (⟨Polynomial.monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I)
    (AffineBlowupChart.powerFraction_numerator_mem I n r)

/-- Every element of an affine blowup chart is represented by a normalized power fraction with
numerator in a power of the center ideal. -/
@[stacks 052Q "affine blowup chart power-fraction representation"]
theorem AffineBlowupChart.exists_powerFraction_eq
    (a : I) (z : R[I / a]) :
    ∃ n : ℕ, ∃ r : ↥(I ^ n),
      z = AffineBlowupChart.powerFraction I a n r := sorry

/-- Evaluation of the Rees algebra at `t = 1` after localizing away from
`a`. -/
@[stacks 07Z3 "Rees algebra evaluation in localization"]
noncomputable def AffineBlowupChart.reesMap (a : I) :
    reesAlgebra I →+* Localization.Away a.1 :=
  (Polynomial.eval₂RingHom (algebraMap R (Localization.Away a.1)) 1).comp
    (reesAlgebra I).toSubring.subtype

/-- The image of the degree-one element `a t` is a unit after localizing away
from `a`. -/
@[stacks 07Z3 "Rees algebra localization parameter is a unit"]
theorem AffineBlowupChart.reesMap_parameter_isUnit (a : I) :
    IsUnit (AffineBlowupChart.reesMap I a (ReesAlgebra.Grading.degreeOne I a)) := sorry

/-- The canonical comparison map from `R[I / a]` to the ordinary localization
`Localization.Away a`. -/
@[stacks 07Z3 "affine blowup chart localization comparison"]
noncomputable def AffineBlowupChart.toLocalizationAway (a : I) :
    R[I / a] →+* Localization.Away a.1 :=
  (IsLocalization.Away.lift (ReesAlgebra.Grading.degreeOne I a)
      (AffineBlowupChart.reesMap_parameter_isUnit I a)).comp
    (algebraMap R[I / a] (Localization.Away (ReesAlgebra.Grading.degreeOne I a)))

namespace AffineBlowupChart

/-- The ordinary localization away from `a` is canonically an algebra over the
affine blowup chart `R[I / a]`. -/
@[stacks 07Z3 "localization algebra over an affine blowup chart"]
instance instAlgebraLocalizationAway (a : I) :
    Algebra R[I / a] (Localization.Away a.1) :=
  RingHom.toAlgebra (AffineBlowupChart.toLocalizationAway I a)

/-- The chart-to-localization comparison map commutes with the canonical map from `R`. -/
@[stacks 07Z3 "affine blowup chart localization map", simp]
theorem toLocalizationAway_algebraMap (I : Ideal R) (a : I) (r : R) :
    toLocalizationAway I a (AffineBlowupChart.algebraMap I a r) =
      algebraMap R (Localization.Away a.1) r := sorry

/-- As ring homomorphisms, the chart-to-localization comparison map composed with
`R → R[I / a]` is the ordinary localization map. -/
@[stacks 07Z3 "affine blowup chart localization map on scalars", simp]
theorem toLocalizationAway_comp_algebraMap (I : Ideal R) (a : I) :
    (toLocalizationAway I a).comp (AffineBlowupChart.algebraMap I a) =
      algebraMap R (Localization.Away a.1) := sorry

end AffineBlowupChart

end
