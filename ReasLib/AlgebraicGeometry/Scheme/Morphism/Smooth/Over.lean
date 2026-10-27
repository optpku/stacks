/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The first projection of a pullback in a scheme slice is smooth when the second
morphism is smooth on underlying schemes. -/
instance instSmoothPullbackFstOver {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z) [Smooth g.left] :
    Smooth (pullback.fst f g).left := sorry

/-- The second projection of a pullback in a scheme slice is smooth when the first
morphism is smooth on underlying schemes. -/
instance instSmoothPullbackSndOver {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z) [Smooth f.left] :
    Smooth (pullback.snd f g).left := sorry

/-- Base change of a smooth morphism along a scheme locally of finite type over the
slice base has source locally of finite type over that base. -/
instance instLocallyOfFiniteTypePullbackSourceOfSmooth
    {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Smooth f.left] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (pullback f g).hom := sorry

end AlgebraicGeometry
