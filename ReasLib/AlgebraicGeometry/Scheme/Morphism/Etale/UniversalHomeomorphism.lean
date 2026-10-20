/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/-- Base change along a universal homeomorphism induces a bijection on morphisms
into an étale scheme over the base. -/
theorem overPullbackMap_bijective_of_universalHomeomorphism
    {S' S : Scheme.{u}} (i : S' ⟶ S) [UniversalHomeomorphism i]
    (X Y : Over S) [Etale X.hom] :
    Function.Bijective (fun g : Y ⟶ X ↦ (Over.pullback i).map g) := sorry

end AlgebraicGeometry.Etale
