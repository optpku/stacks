/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

/-!
# Picard groups and closed immersions

This file records the surjectivity of Picard pullback along closed immersions
into one-dimensional Noetherian schemes.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Z : Scheme.{u}}

/-- Pullback along a closed immersion into a Noetherian scheme of topological
Krull dimension at most one is surjective on Picard groups. -/
theorem picardPullback_surjective_of_isClosedImmersion
    (i : Z ⟶ X) [IsClosedImmersion i] [TopologicalSpace.NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) :
    Function.Surjective (Scheme.Hom.picardPullback i) := sorry

end AlgebraicGeometry.Scheme.Hom
