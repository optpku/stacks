/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Proper

/-!
# Proper morphisms of formal algebraic spaces

A morphism of functors of points on schemes over `S` is proper when it is
representable by algebraic spaces and every Yoneda pullback is a proper
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

#check (Proper :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y), Prop)

#check (Proper.id :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}, Proper (𝟙 X))

#check (Proper.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsIso f], Proper f)

#check (Proper.iff_relativeAlgebraicSpaces :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y),
    Proper f ↔ AlgebraicSpace.relativeAlgebraicSpaces (@AlgebraicSpace.Proper S) f)

end AlgebraicGeometry.FormalAlgebraicSpace
