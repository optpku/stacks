module

public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_24_2_Lambda

/-!
# Geometric points of large algebraically closed fields

Geometric points of an algebraic space cover its underlying point space, and
surjectivity of a morphism of algebraic spaces is detected on algebraically
closed points of cardinality larger than `lambda` of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.24.2 (1): as `k` ranges over all algebraically closed fields over
`S`, the geometric points of `Y` cover `|Y|`. -/
@[stacks 0488]
theorem geometricPoints_surjective {S : Scheme.{u}} {Y : AlgebraicSpace S} :
    Function.Surjective (GeometricPoint.image : GeometricPoint Y → Points Y) :=
  sorry

/-- Lemma 67.24.2 (2): as `k` ranges over algebraically closed fields over `S`
with `#k ≥ lambda Y` and `#k > lambda X`, the geometric points of `Y` cover
`|Y|`. -/
@[stacks 0488]
theorem geometricPoints_surjective_of_lambda {S : Scheme.{u}} (X Y : AlgebraicSpace S)
    (y : Points Y) :
    ∃ ybar : GeometricPoint Y,
      lambda Y ≤ #ybar.K ∧ lambda X < #ybar.K ∧ ybar.image = y :=
  sorry

/-- Lemma 67.24.2 (3): for a geometric point `sbar : Spec k ⟶ S` with
`#k > lambda X`, the map `X(k) → |X_s|` is surjective, where `|X_s|` is the
fibre of `Points.base` at the image of `sbar`. -/
@[stacks 0488]
theorem fieldPoints_surjective_fiber {S : Scheme.{u}} (X : AlgebraicSpace S)
    (sbar : Scheme.GeometricPoint S) (h : lambda X < #sbar.K) (x : Points X)
    (hx : Points.base x = sbar.image) :
    ∃ p : ofOver (Over.mk sbar.hom) ⟶ X, fieldPointsToPoints sbar.hom p = x :=
  sorry

/-- Lemma 67.24.2 (4): for a morphism `f : X ⟶ Y` of algebraic spaces over `S`
and a geometric point `sbar : Spec k ⟶ S` with `#k > lambda X`, the map
`X(k) → |X| ×_{|Y|} Y(k)` is surjective. -/
@[stacks 0488]
theorem fieldPoints_surjective_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (sbar : Scheme.GeometricPoint S) (h : lambda X < #sbar.K) :
    Function.Surjective (toPullbackFieldPoints f sbar.hom) :=
  sorry

/-- Lemma 67.24.2 (5): a morphism `f : X ⟶ Y` of algebraic spaces over `S` is
surjective if and only if `X(k) → Y(k)` is surjective for every algebraically
closed field `k` over `S` with `#k > lambda X` and `#k ≥ lambda Y`. -/
@[stacks 0488]
theorem surjective_iff_surjectiveOnLargeFieldPoints {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Surjective f ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (σ : Spec (.of K) ⟶ S),
        lambda X < #K → lambda Y ≤ #K →
          Function.Surjective (fun p : ofOver (Over.mk σ) ⟶ X ↦ p ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
