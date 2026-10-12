/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.Criteria
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.SmoothLocus
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic

/-!
# Relative Frobenius of varieties

This file records reducedness, variety, and function-field degree properties of the relative
Frobenius of a variety over a field of positive characteristic.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {p : ℕ} {k : Type u} [Field k] [Fact p.Prime] [CharP k p]

/-- The relative Frobenius target of a geometrically reduced variety is again a variety over the
base field. -/
theorem relativeFrobeniusTarget_variety_of_geometricallyReduced
    (X : SchemeOverField k) [Variety X] (hgeom : geometricallyReduced X) :
    Variety (Scheme.Hom.relativeFrobeniusTargetOver (p := p) X.hom) := sorry

/-- The function-field degree induced by the relative Frobenius of a geometrically reduced
variety is the characteristic raised to the transcendence degree at its generic point. -/
theorem relativeFrobenius_inducedFunctionFieldDegree_eq_pow
    (X : SchemeOverField k) [Variety X] (hgeom : geometricallyReduced X) :
    -- Local instance justification (defeq pin): expose proved integrality of the canonical target.
    letI : IsIntegral (Scheme.Hom.relativeFrobeniusTarget (p := p) X.hom) :=
      (relativeFrobeniusTarget_variety_of_geometricallyReduced (p := p) X hgeom).toIsIntegral
    (Scheme.Hom.relativeFrobenius (p := p) X.hom).inducedFunctionFieldDegree =
      p ^ baseFieldTrdegAt X (genericPoint X.left) := sorry

/-- For a variety in positive characteristic, reducedness of the relative Frobenius target,
geometric reducedness, and the existence of a nonempty smooth open are equivalent; under these
conditions the target is a variety and the relative Frobenius is finite, dominant, and has the
expected function-field degree. -/
theorem relativeFrobenius_variety_tfae_and_properties
    (X : SchemeOverField k) [Variety X] :
    List.TFAE [
      IsReduced (Scheme.Hom.relativeFrobeniusTarget (p := p) X.hom),
      geometricallyReduced X,
      ∃ U : X.left.Opens, U ≠ ⊥ ∧ Smooth (U.ι ≫ X.hom)
    ] ∧
      ∀ hgeom : geometricallyReduced X,
        Variety (Scheme.Hom.relativeFrobeniusTargetOver (p := p) X.hom) ∧
          IsFinite (Scheme.Hom.relativeFrobenius (p := p) X.hom) ∧
          IsDominant (Scheme.Hom.relativeFrobenius (p := p) X.hom) ∧
          (
           -- Local instance justification (defeq pin): expose proved integrality of the canonical target.
           letI : IsIntegral (Scheme.Hom.relativeFrobeniusTarget (p := p) X.hom) :=
             (relativeFrobeniusTarget_variety_of_geometricallyReduced
               (p := p) X hgeom).toIsIntegral
           (Scheme.Hom.relativeFrobenius (p := p) X.hom).inducedFunctionFieldDegree =
             p ^ baseFieldTrdegAt X (genericPoint X.left)) := sorry

end AlgebraicGeometry.SchemeOverField
