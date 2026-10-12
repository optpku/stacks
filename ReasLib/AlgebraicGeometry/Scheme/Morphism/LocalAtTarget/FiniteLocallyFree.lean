/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFinitePresentation

/-!
# Target locality of finite local freeness

This file records target locality of finite local freeness and fixed rank for
morphisms of schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsFiniteLocallyFree

/-- Finite locally free morphisms of schemes are local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsFiniteLocallyFree : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsFiniteLocallyFree

namespace AlgebraicGeometry.IsFiniteLocallyFreeOfRank

/-- Finite locally free morphisms of fixed rank are local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc (d : ℕ) :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f ↦ AlgebraicGeometry.IsFiniteLocallyFreeOfRank f d) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsFiniteLocallyFreeOfRank
