/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.CompleteIntersection.Local
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Purity

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- A Noetherian local complete-intersection ring of Krull dimension at least three
has purity: every finite étale cover of its punctured spectrum extends over its spectrum. -/
@[stacks 0BPD, instance]
instance hasPurity_of_completeIntersectionLocalRing
    {A : Type u} [CommRing A] [IsCompleteIntersectionLocalRing A]
    [Fact (3 ≤ ringKrullDim A)] :
    HasPurity A := sorry

/-- Finite étale covers of the punctured spectrum of a complete-intersection local
ring of Krull dimension at least three extend over the spectrum. -/
theorem finiteEtale_extends_of_completeIntersectionLocalRing
    {A : Type u} [CommRing A] [IsCompleteIntersectionLocalRing A]
    [Fact (3 ≤ ringKrullDim A)] :
    ∀ V : Scheme.FiniteEtale (scheme A),
      ∃ Y : Scheme.FiniteEtale (Spec (CommRingCat.of A)),
        Nonempty ((Scheme.finiteEtaleBaseChange (puncturedOpen A).ι).obj Y ≅ V) := sorry

end AlgebraicGeometry.PuncturedSpectrum
