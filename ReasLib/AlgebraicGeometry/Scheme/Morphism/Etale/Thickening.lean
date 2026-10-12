/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/-- Base change along a thickening induces a bijection on morphisms into an étale
scheme over the base. -/
theorem overPullbackMap_bijective_of_isThickening
    {S₀ S : Scheme.{u}} (i : S₀ ⟶ S) [IsThickening i]
    (X Y : Over S) [Etale X.hom] :
    Function.Bijective (fun f : Y ⟶ X ↦ (Over.pullback i).map f) := sorry

end AlgebraicGeometry.Etale
