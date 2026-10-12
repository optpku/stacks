/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Compactification
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ClosedPoint

/-!
# Compactifications of curves

This file records regular projective compactifications of curves and their smooth variants over
perfect fields, together with projective compactifications factoring morphisms to proper varieties.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k]

/-- A regular curve over a field admits an open immersion into a regular projective curve whose
complement is a finite set of closed points. -/
theorem exists_regularProjectiveCompactification
    (X : Over (Spec (CommRingCat.of k))) [Curve X] [Scheme.Regular X.left] :
    ∃ (Xbar : Over (Spec (CommRingCat.of k))) (j : X.left ⟶ Xbar.left) (hj : IsOpenImmersion j),
      let U : Xbar.left.Opens := @Scheme.Hom.opensRange _ _ j hj
      j ≫ Xbar.hom = X.hom ∧
        Curve Xbar ∧
        Scheme.Regular Xbar.left ∧
        Projective Xbar.hom ∧
        Set.Finite ((U : Set Xbar.left)ᶜ) ∧
        ∀ x ∈ ((U : Set Xbar.left)ᶜ), x ∈ closedPoints Xbar.left := sorry

/-- A regular curve over a perfect field is smooth over that field. -/
theorem smooth_of_regular_of_perfectField
    (X : Over (Spec (CommRingCat.of k))) [Curve X] [Scheme.Regular X.left] [PerfectField k] :
    Smooth X.hom := sorry

/-- A regular curve over a perfect field admits an open immersion into a smooth regular projective
curve whose complement is a finite set of closed points. -/
theorem exists_smoothProjectiveCompactification_of_regular_of_perfectField
    (X : Over (Spec (CommRingCat.of k))) [Curve X] [Scheme.Regular X.left] [PerfectField k] :
    ∃ (Xbar : Over (Spec (CommRingCat.of k))) (j : X.left ⟶ Xbar.left) (hj : IsOpenImmersion j),
      let U : Xbar.left.Opens := @Scheme.Hom.opensRange _ _ j hj
      j ≫ Xbar.hom = X.hom ∧
        Curve Xbar ∧
        Scheme.Regular Xbar.left ∧
        Projective Xbar.hom ∧
        Smooth Xbar.hom ∧
        Set.Finite ((U : Set Xbar.left)ᶜ) ∧
        ∀ x ∈ ((U : Set Xbar.left)ᶜ), x ∈ closedPoints Xbar.left := sorry

/-- A morphism from a curve to a proper variety over a field factors through an open immersion
into a projective curve. -/
theorem exists_factor_through_projective_curve
    {X Y : SchemeOverField k} [Curve X] [Variety Y] [IsProper Y.hom] (f : X ⟶ Y) :
    ∃ (Xbar : SchemeOverField k) (j : X ⟶ Xbar) (g : Xbar ⟶ Y)
      (_ : IsOpenImmersion j.left) (_ : Curve Xbar) (_ : Projective Xbar.hom),
      j ≫ g = f := sorry

end AlgebraicGeometry.Curve
