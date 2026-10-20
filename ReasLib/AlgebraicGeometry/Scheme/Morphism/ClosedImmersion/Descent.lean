/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Descent of closed immersions

This file gives a descent criterion for closed immersions along point-bijective closed
immersions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.IsClosedImmersion

/-- A morphism is a closed immersion if its pullback along a point-bijective closed immersion is
a closed immersion and the requisite finite type or finite presentation condition holds. -/
theorem of_pullback_snd_of_bijective
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hg : IsClosedImmersion g)
    (hg_bij : Function.Bijective ⇑(ConcreteCategory.hom g.base))
    (hpullback : IsClosedImmersion (pullback.snd f g))
    (hfinite : Scheme.Hom.FiniteType f ∨ Scheme.Hom.FinitePresentation g) :
    IsClosedImmersion f := sorry

end AlgebraicGeometry.IsClosedImmersion
