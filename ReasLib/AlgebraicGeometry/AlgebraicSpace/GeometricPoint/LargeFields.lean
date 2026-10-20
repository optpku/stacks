/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Lambda

/-!
# Geometric points over large algebraically closed fields

Geometric points cover an algebraic space, and sufficiently large algebraically
closed fields lift underlying points compatibly with morphisms. Surjectivity is
detected on field-valued points satisfying the residue-field cardinal bounds.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

namespace AlgebraicGeometry.AlgebraicSpace

/-- As `k` ranges over all algebraically closed fields over
`S`, the geometric points of `Y` cover `|Y|`. -/
theorem geometricPoints_surjective {S : Scheme.{u}} {Y : AlgebraicSpace S} :
    Function.Surjective (GeometricPoint.image : GeometricPoint Y → Points Y) :=
  sorry

/-- As `k` ranges over algebraically closed fields over `S`
with `#k ≥ lambda Y` and `#k > lambda X`, the geometric points of `Y` cover
`|Y|`. -/
theorem geometricPoints_surjective_of_lambda {S : Scheme.{u}} (X Y : AlgebraicSpace S)
    (y : Points Y) :
    ∃ ybar : GeometricPoint Y,
      lambda Y ≤ #ybar.K ∧ lambda X < #ybar.K ∧ ybar.image = y :=
  sorry

/-- For a geometric point `sbar : Spec k ⟶ S` with
`#k > lambda X`, the map `X(k) → |X_s|` is surjective, where `|X_s|` is the
fibre of `Points.base` at the image of `sbar`. -/
theorem fieldPoints_surjective_fiber {S : Scheme.{u}} (X : AlgebraicSpace S)
    (sbar : Scheme.GeometricPoint S) (h : lambda X < #sbar.K) (x : Points X)
    (hx : Points.base x = sbar.image) :
    ∃ p : ofOver (Over.mk sbar.hom) ⟶ X, fieldPointsToPoints sbar.hom p = x :=
  sorry

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S`
and a geometric point `sbar : Spec k ⟶ S` with `#k > lambda X`, the map
`X(k) → |X| ×_{|Y|} Y(k)` is surjective. -/
theorem fieldPoints_surjective_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (sbar : Scheme.GeometricPoint S) (h : lambda X < #sbar.K) :
    Function.Surjective (toPullbackFieldPoints f sbar.hom) :=
  sorry

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is
surjective if and only if `X(k) → Y(k)` is surjective for every algebraically
closed field `k` over `S` with `#k > lambda X` and `#k ≥ lambda Y`. -/
theorem surjective_iff_surjectiveOnLargeFieldPoints {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Surjective f ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (σ : Spec (.of K) ⟶ S),
        lambda X < #K → lambda Y ≤ #K →
          Function.Surjective (fun p : ofOver (Over.mk σ) ⟶ X ↦ p ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
