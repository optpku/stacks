/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianMonoidal

/-! Restriction of group algebraic-space actions along invariant morphisms. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable (G : GroupAlgebraicSpace B) (X : Action G)

/-- The morphism `(G ×_B F) ×_F X ⟶ G` over `B`. -/
def restrictToSmulHomG {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F) :
    Over.mk (((GroupAlgebraicSpace.baseChange G f).X ⊗ Over.mk q).hom ≫ f) ⟶
      G.X :=
  Over.homMk
    ((fst (GroupAlgebraicSpace.baseChange G f).X (Over.mk q)).left ≫
      CategoryTheory.Limits.pullback.fst G.X.hom f)
    (by sorry)

/-- The morphism `(G ×_B F) ×_F X ⟶ X` over `B`. -/
def restrictToSmulHomX {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom) :
    Over.mk (((GroupAlgebraicSpace.baseChange G f).X ⊗ Over.mk q).hom ≫ f) ⟶
      X.X :=
  Over.homMk
    (snd (GroupAlgebraicSpace.baseChange G f).X (Over.mk q)).left
    (by sorry)

/-- The left component of `restrictToSmulHomG` is the composite of the first
projection with the canonical categorical pullback projection to `G`. -/
theorem restrictToSmulHomG_left {F : AlgebraicSpace S} (f : F ⟶ B)
    (q : X.X.left ⟶ F) :
    (restrictToSmulHomG G X f q).left =
      (fst (GroupAlgebraicSpace.baseChange G f).X (Over.mk q)).left ≫
        CategoryTheory.Limits.pullback.fst G.X.hom f := sorry

/-- The left component of `restrictToSmulHomX` is the second projection. -/
theorem restrictToSmulHomX_left {F : AlgebraicSpace S} (f : F ⟶ B)
    (q : X.X.left ⟶ F) (hq : q ≫ f = X.X.hom) :
    (restrictToSmulHomX G X f q hq).left =
      (snd (GroupAlgebraicSpace.baseChange G f).X (Over.mk q)).left := sorry

/-- The underlying algebraic-space map of the restricted `G_F`-action, obtained by
transporting `γ[G.X, X.X]` along the cartesian comparison
`(G ×_B F) ×_F X ⟶ G ×_B X`. -/
def restrictToSmulLeft {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom) :
    ((GroupAlgebraicSpace.baseChange G f).X ⊗ Over.mk q).left ⟶ (Over.mk q).left :=
  (CartesianMonoidalCategory.lift
      (restrictToSmulHomG G X f q) (restrictToSmulHomX G X f q hq)).left ≫
    γ[G.X, X.X].left

/-- The restricted action morphism of `G_F` on `X` in `Over F`. -/
def restrictToSmul {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    (GroupAlgebraicSpace.baseChange G f).X ⊗ Over.mk q ⟶ Over.mk q :=
  Over.homMk (restrictToSmulLeft G X f q hq)
    (by sorry)

/-- The left component of `restrictToSmul` is `restrictToSmulLeft`. -/
theorem restrictToSmul_left {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    (restrictToSmul G X f q hq h_eq).left = restrictToSmulLeft G X f q hq := sorry

/-- The identity-action law for `restrictToSmul`. -/
theorem restrictToSmul_one_smul {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    η[(GroupAlgebraicSpace.baseChange G f).X] ⊵ₗ Over.mk q ≫
        restrictToSmul G X f q hq h_eq =
      (λₗ (Over.mk q)).hom := sorry

/-- The multiplication-action law for `restrictToSmul`. -/
theorem restrictToSmul_mul_smul {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    μ[(GroupAlgebraicSpace.baseChange G f).X] ⊵ₗ Over.mk q ≫
        restrictToSmul G X f q hq h_eq =
      (αₗ (GroupAlgebraicSpace.baseChange G f).X
          (GroupAlgebraicSpace.baseChange G f).X (Over.mk q)).hom ≫
        (GroupAlgebraicSpace.baseChange G f).X ⊴ₗ
            restrictToSmul G X f q hq h_eq ≫
          restrictToSmul G X f q hq h_eq := sorry

/-- The `G_F`-action on `X` over `F` obtained from a `G`-action on `X` over `B`
along an invariant morphism `q : X ⟶ F` over `B`. -/
def restrictTo {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    Action (GroupAlgebraicSpace.baseChange G f) where
  X := Over.mk q
  mod :=
    { smul := restrictToSmul G X f q hq h_eq
      one_smul := restrictToSmul_one_smul G X f q hq h_eq
      mul_smul := restrictToSmul_mul_smul G X f q hq h_eq }

/-- The carrier of `restrictTo` is `X` viewed over `F` via `q`. -/
theorem restrictTo_X {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    (restrictTo G X f q hq h_eq).X = Over.mk q := sorry

/-- The stored action morphism of `restrictTo` is `restrictToSmul`. -/
theorem restrictTo_smul {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    (restrictTo G X f q hq h_eq).mod.smul = restrictToSmul G X f q hq h_eq := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Action
