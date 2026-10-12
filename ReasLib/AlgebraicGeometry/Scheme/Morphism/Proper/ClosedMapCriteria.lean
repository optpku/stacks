/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyClosed.FinitePresentation

/-!
# Closed-map criteria for proper morphisms

Properness of a separated finite-type morphism can be tested by closedness after locally
finite-type base changes or after base change to finite-dimensional relative affine spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsProper

/-- For a separated finite-type morphism, properness, closedness after every locally finite-type
base change, and closedness after every finite-dimensional relative affine-space base change
are equivalent. -/
theorem tfae_isClosedMap_baseChange
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [Scheme.Hom.FiniteType f] :
    List.TFAE
      [ AlgebraicGeometry.IsProper f
      , ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S), LocallyOfFiniteType g →
          IsClosedMap (pullback.snd f g).base
      , ∀ n : ℕ,
          IsClosedMap (pullback.snd f (AffineSpace (ULift.{u} (Fin n)) S ↘ S)).base
      ] := sorry

end AlgebraicGeometry.IsProper
