/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Point.TypeImage
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Topos points induced by site points

This module constructs the geometric point of `Sh(C, J)` induced by a point of
the site and records its canonical `Type`-valued inverse- and direct-image
comparisons.
-/

@[expose] public section

open CategoryTheory

universe u v w

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A point of a site induces a `Type`-valued point of its sheaf topos. -/
@[stacks 00YA "(1)"]
noncomputable def toToposPoint
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    MorphismOfTopoiIn J typesGrothendieckTopology.{w} where
  inverseImageFunctor := LeftExactFunctor.of (p.sheafFiber ⋙ typeEquiv.{w}.functor)
  pushforward := typeEquiv.{w}.inverse ⋙ p.skyscraperSheafFunctor
  adjunction := p.skyscraperSheafAdjunction.comp typeEquiv.{w}.toAdjunction

/-- The `Type`-valued inverse image of the point induced from `p` is canonically its sheaf
fiber functor. -/
noncomputable def toToposPoint_pointInverseImageIso
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    p.toToposPoint.typeInverseImage ≅ p.sheafFiber :=
  (Functor.associator p.sheafFiber typeEquiv.{w}.functor typeEquiv.{w}.inverse).symm ≪≫
    (Functor.isoWhiskerLeft p.sheafFiber typeEquiv.{w}.unitIso.symm) ≪≫
      Functor.rightUnitor p.sheafFiber

/-- The `Type`-valued direct image of the point induced from `p` is canonically its skyscraper
sheaf functor. -/
noncomputable def toToposPoint_pointPushforwardIso
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    p.toToposPoint.typePushforward ≅ p.skyscraperSheafFunctor :=
  (Functor.associator typeEquiv.{w}.functor typeEquiv.{w}.inverse p.skyscraperSheafFunctor).symm ≪≫
    (Functor.isoWhiskerRight typeEquiv.{w}.unitIso.symm p.skyscraperSheafFunctor) ≪≫
      Functor.leftUnitor p.skyscraperSheafFunctor

end CategoryTheory.GrothendieckTopology.Point
