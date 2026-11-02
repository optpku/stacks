/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.BaseChange
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Slice pullback of actions of group algebraic spaces

Pulling a `G`-action back along `f : B' ⟶ B` yields a
`baseChange G f`-action, together with the comparison of iterated
group pullbacks and transport of actions along group isomorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The action morphism of a slice-pulled module object. -/
def pullbackActionSmul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    (baseChange G f).X ⊗ (CategoryTheory.Over.pullback f).obj X.X ⟶ (CategoryTheory.Over.pullback f).obj X.X :=
  Functor.LaxMonoidal.μ (CategoryTheory.Over.pullback f) G.X X.X ≫ (CategoryTheory.Over.pullback f).map X.mod.smul

/-- The identity-action law for a slice-pulled module object. -/
theorem pullbackAction_one_smul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    η[(baseChange G f).X] ⊵ₗ (CategoryTheory.Over.pullback f).obj X.X ≫ pullbackActionSmul f G X =
      (λₗ ((CategoryTheory.Over.pullback f).obj X.X)).hom := by
  let F := CategoryTheory.Over.pullback f
  change ((Functor.LaxMonoidal.ε F ≫ F.map η[G.X]) ▷ F.obj X.X) ≫
      (Functor.LaxMonoidal.μ F G.X X.X ≫ F.map X.mod.smul) = (λ_ _).hom
  simp [comp_whiskerRight, ← F.map_comp]

/-- The multiplication-action law for a slice-pulled module object. -/
theorem pullbackAction_mul_smul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    μ[(baseChange G f).X] ⊵ₗ (CategoryTheory.Over.pullback f).obj X.X ≫ pullbackActionSmul f G X =
      (αₗ (baseChange G f).X (baseChange G f).X
          ((CategoryTheory.Over.pullback f).obj X.X)).hom ≫
        (baseChange G f).X ⊴ₗ pullbackActionSmul f G X ≫
          pullbackActionSmul f G X := by
  let F := CategoryTheory.Over.pullback f
  change ((Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X]) ▷ F.obj X.X) ≫
      (Functor.LaxMonoidal.μ F G.X X.X ≫ F.map X.mod.smul) =
    (α_ _ _ _).hom ≫ F.obj G.X ◁
      (Functor.LaxMonoidal.μ F G.X X.X ≫ F.map X.mod.smul) ≫
        Functor.LaxMonoidal.μ F G.X X.X ≫ F.map X.mod.smul
  simp_rw [comp_whiskerRight, Category.assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc, whiskerLeft_comp, Category.assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc]
  slice_lhs 3 4 => rw [← F.map_comp, ModObj.mul_smul_self]
  simp

/-- Slice pullback of a `G`-action along `f : B' ⟶ B`. -/
def pullbackAction {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) : Action (baseChange G f) where
  X := (CategoryTheory.Over.pullback f).obj X.X
  mod :=
    { smul := pullbackActionSmul f G X
      one_smul := pullbackAction_one_smul f G X
      mul_smul := pullbackAction_mul_smul f G X }

/-- The underlying object of a pulled-back action is the slice pullback of the
original object. -/
theorem pullbackAction_X {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    (pullbackAction f G X).X = (CategoryTheory.Over.pullback f).obj X.X := rfl

/-- The action morphism of `pullbackAction f G X` is `pullbackActionSmul`. -/
theorem pullbackAction_smul {S : Scheme.{u}} {B B' : AlgebraicSpace S} (f : B' ⟶ B)
    (G : GroupAlgebraicSpace B) (X : Action G) :
    (pullbackAction f G X).mod.smul = pullbackActionSmul f G X := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Comparison of group objects `G_{B''}` obtained by pulling back along a
composite versus pulling back in stages. -/
def baseChangeCompIso {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (G : GroupAlgebraicSpace B) :
    baseChange G (g ≫ f) ≅ baseChange (baseChange G f) g :=
  Grp.mkIso ((CategoryTheory.Over.pullbackComp g f).app G.X)
    (by
      let e : baseChange G (g ≫ f) ≅ baseChange (baseChange G f) g :=
        (Functor.mapGrpNatIso (CategoryTheory.Over.pullbackComp g f) ≪≫
        Functor.mapGrpCompIso).app G
      have he : e.hom.hom.hom = ((CategoryTheory.Over.pullbackComp g f).app G.X).hom := by
        change ((CategoryTheory.Over.pullbackComp g f).app G.X).hom ≫ 𝟙 _ = _
        exact Category.comp_id _
      simpa only [he] using IsMonHom.one_hom e.hom.hom.hom)
    (by
      let e : baseChange G (g ≫ f) ≅ baseChange (baseChange G f) g :=
        (Functor.mapGrpNatIso (CategoryTheory.Over.pullbackComp g f) ≪≫
        Functor.mapGrpCompIso).app G
      have he : e.hom.hom.hom = ((CategoryTheory.Over.pullbackComp g f).app G.X).hom := by
        change ((CategoryTheory.Over.pullbackComp g f).app G.X).hom ≫ 𝟙 _ = _
        exact Category.comp_id _
      simpa only [he] using IsMonHom.mul_hom e.hom.hom.hom)

/-- The underlying slice map of `baseChangeCompIso` is the component of
the canonical slice-pullback composition isomorphism. -/
theorem baseChangeCompIso_hom {S : Scheme.{u}} {B B' B'' : AlgebraicSpace S}
    (f : B' ⟶ B) (g : B'' ⟶ B') (G : GroupAlgebraicSpace B) :
    (baseChangeCompIso f g G).hom.hom.hom =
      ((CategoryTheory.Over.pullbackComp g f).app G.X).hom := rfl

end AlgebraicGeometry.GroupAlgebraicSpace
