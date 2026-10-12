/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Testing universal openness after finitely presented base changes

Universal openness can be tested either after locally finitely presented base changes or after
base change to relative affine spaces of finite dimension.
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.UniversallyOpen

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A morphism is universally open if and only if its base change along every finite-dimensional
relative affine-space projection is an open map. -/
theorem iff_isOpenMap_affineSpace_baseChange :
    AlgebraicGeometry.UniversallyOpen f ↔
      ∀ n : ℕ,
        IsOpenMap (pullback.snd f (AffineSpace (ULift.{u} (Fin n)) S ↘ S)).base := sorry

/-- A morphism is universally open if and only if its base change along every locally finitely
presented morphism is an open map. -/
theorem iff_isOpenMap_baseChange_of_locallyOfFinitePresentation :
    AlgebraicGeometry.UniversallyOpen f ↔
      ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S), LocallyOfFinitePresentation g →
        IsOpenMap (pullback.snd f g).base := sorry

end AlgebraicGeometry.UniversallyOpen
