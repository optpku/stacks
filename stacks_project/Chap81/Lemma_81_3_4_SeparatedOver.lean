/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SeparatedOver

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.separatedMorphismOverProperty :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S), ObjectProperty (Over B))

#check (AlgebraicGeometry.AlgebraicSpace.SeparatedMorphismOver :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S), Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.SeparatedMorphismOver.inclusion :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.SeparatedMorphismOver B ⥤ Over B)

#check (AlgebraicGeometry.AlgebraicSpace.IsColimitAmongSeparated :
  ∀ {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
    {D : J ⥤ Over B} (c : Cocone D), Prop)
