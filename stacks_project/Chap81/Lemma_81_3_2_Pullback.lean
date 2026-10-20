/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.Cocone
public import stacks_project.Chap65.Lemma_65_7_3_Pullback

/-!
# Base change of cocones of algebraic spaces

The canonical base-change cocone and the structural maps of pairwise overlaps.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v w

#check (AlgebraicGeometry.AlgebraicSpace.baseChangeCocone :
  ∀ {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
    {D : J ⥤ Over B} (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left), Cocone (baseChangeDiagram c f))

#check (AlgebraicGeometry.AlgebraicSpace.overlapHom :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type w}
    (family : ι → Over X) (a b : ι),
    overPullbackObj (family b).hom (family a) ⟶ X)
