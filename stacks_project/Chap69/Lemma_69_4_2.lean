module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap66.Definition_66_19_6_Stalk
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap69.Lemma_69_4_2_Over

/-!
# Stalks of the pushforward along a finite morphism of algebraic spaces

For a finite morphism of algebraic spaces, the stalk of `f_* F` at a geometric point is the
product of the stalks of `F` at the finitely many same-field geometric lifts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
variable (ybar : GeometricPoint Y)

/-- The family of small-étale stalks of a set-valued sheaf at the same-field geometric
points of `X` over `ybar`. -/
def finitePushforwardStalkFamily (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    GeometricPoint.Over f ybar → Type (u + 1) :=
  fun x ↦ GeometricPoint.stalk x.toGeometricPoint F.obj

/-- The value of `finitePushforwardStalkFamily` at a point over `ybar`. -/
theorem finitePushforwardStalkFamily_apply
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (x : GeometricPoint.Over f ybar) :
    finitePushforwardStalkFamily f ybar F x =
      GeometricPoint.stalk x.toGeometricPoint F.obj :=
  sorry

/-- Lemma 69.4.2: for a finite morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
and a geometric point `ybar` of `Y`, the small-étale stalk of `f_* F` at `ybar` is the
product of the stalks of `F` at the same-field geometric lifts of `ybar` to `X`. -/
@[stacks 0DK3]
theorem finite_pushforward_stalk_product
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIsomorphic
      (GeometricPoint.stalk ybar ((sheafPushforwardType f).obj F).obj)
      ((x : GeometricPoint.Over f ybar) → finitePushforwardStalkFamily f ybar F x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
