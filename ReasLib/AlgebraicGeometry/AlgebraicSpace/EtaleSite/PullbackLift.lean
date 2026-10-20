/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Localization

/-!
# Induced arrow into a spaces-étale pullback

A commutative square of algebraic spaces with étale vertical arrows determines the
comparison arrow `c : U ⟶ V ×_Y X` in `X_spaces,étale`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}

/-- The arrow `c : U ⟶ V ×_Y X` in `X_spaces,étale` induced by a commutative square with étale
vertical morphisms. -/
def spacesEtalePullbackLift (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y)
    [Etale p] [Etale q] (hcomm : p ≫ f = g ≫ q) :
    spacesEtaleSite.mk p ⟶ (spacesEtalePullback f).obj (spacesEtaleSite.mk q) :=
  MorphismProperty.Over.homMk (pullback.lift g p hcomm.symm) (pullback.lift_snd g p hcomm.symm)

/-- The underlying algebraic-space morphism of `spacesEtalePullbackLift` is
`pullback.lift g p hcomm.symm`. -/
@[simp]
theorem spacesEtalePullbackLift_left (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y)
    [Etale p] [Etale q] (hcomm : p ≫ f = g ≫ q) :
    (spacesEtalePullbackLift p g f q hcomm).left = pullback.lift g p hcomm.symm :=
  rfl

/-- The lift `c` projects to `g` along `pullback.fst`. -/
theorem spacesEtalePullbackLift_fst (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y)
    [Etale p] [Etale q] (hcomm : p ≫ f = g ≫ q) :
    (spacesEtalePullbackLift p g f q hcomm).left ≫ pullback.fst q f = g :=
  pullback.lift_fst g p hcomm.symm

/-- The lift `c` projects to `p` along `pullback.snd`. -/
theorem spacesEtalePullbackLift_snd (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y)
    [Etale p] [Etale q] (hcomm : p ≫ f = g ≫ q) :
    (spacesEtalePullbackLift p g f q hcomm).left ≫ pullback.snd q f = p :=
  pullback.lift_snd g p hcomm.symm

end AlgebraicGeometry.AlgebraicSpace
