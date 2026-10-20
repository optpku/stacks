/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap69.Lemma_69_20_4_Pullback
public import stacks_project.Chap71.Definition_71_7_6_ZeroScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection.Pullback

/-!
# Pullback of zero schemes of invertible modules on algebraic spaces

A morphism of algebraic spaces pulls an invertible module and a global section
back to another such pair, and the resulting zero schemes form a cartesian
square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)
variable [isInvertibleObject ((Modules.pullback f).obj L)]

#check (AlgebraicGeometry.AlgebraicSpace.zeroIdealSubobject_sectionsPullback f L s :
    zeroIdealSubobject ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s) =
      (zeroScheme L s).idealSheaf.pullback f)

#check (AlgebraicGeometry.AlgebraicSpace.vanishes_zeroIdealSubobject_sectionsPullback f L s :
    ∀ {T : (Over S)ᵒᵖ} {h : X'.functorOfPoints.obj T},
      vanishes (homOfPoint h)
          (zeroIdealSubobject ((Modules.pullback f).obj L)
            (Modules.sectionsPullback f L s)) →
        vanishes (homOfPoint (f.app T h)) (zeroIdealSubobject L s))

#check (AlgebraicGeometry.AlgebraicSpace.zeroSchemePullbackMap f L s :
    (zeroScheme ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s)).X ⟶
      (zeroScheme L s).X)

#check (AlgebraicGeometry.AlgebraicSpace.zeroSchemePullbackMap_comp f L s :
    zeroSchemePullbackMap f L s ≫ zeroSchemeι L s =
      zeroSchemeι ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s) ≫ f)

#check (AlgebraicGeometry.AlgebraicSpace.zeroSchemePullbackSquare f L s :
    IsPullback
      (zeroSchemeι ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s))
      (zeroSchemePullbackMap f L s) f (zeroSchemeι L s))

end AlgebraicGeometry.AlgebraicSpace
