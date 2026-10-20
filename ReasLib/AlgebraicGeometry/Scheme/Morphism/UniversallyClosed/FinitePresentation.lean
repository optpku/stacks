module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Testing universal closedness after finitely presented base changes

Universal closedness of a quasi-compact morphism can be tested either after locally finitely
presented base changes or after base change to relative affine spaces of finite dimension.
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.UniversallyClosed

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]

/-- A quasi-compact morphism is universally closed if and only if its base change along every
locally finitely presented morphism is a closed map. -/
theorem iff_isClosedMap_baseChange_of_locallyOfFinitePresentation :
    AlgebraicGeometry.UniversallyClosed f ↔
      ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S), LocallyOfFinitePresentation g →
        IsClosedMap (pullback.snd f g).base := sorry

/-- A quasi-compact morphism is universally closed if and only if its base change along every
finite-dimensional relative affine-space projection is a closed map. -/
theorem iff_isClosedMap_affineSpace_baseChange :
    AlgebraicGeometry.UniversallyClosed f ↔
      ∀ n : ℕ,
        IsClosedMap (pullback.snd f (AffineSpace (ULift.{u} (Fin n)) S ↘ S)).base := sorry

end AlgebraicGeometry.UniversallyClosed
