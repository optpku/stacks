/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.LocalRing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat

noncomputable section

universe u

/- Exercise 111.42.4: let `X` be the spectrum of a local ring. Then `F.H' i ⊤` is zero
for every `0 < i` and any sheaf of abelian groups `F`. -/
@[stacks 0D8T]
#check
  (TopCat.Sheaf.Cohomology.isZero_higherCohomology_of_isLocalRing :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      (F : (PrimeSpectrum.Top R).Sheaf AddCommGrpCat.{u}) {i : ℕ},
      0 < i → IsZero (F.H' i (⊤ : Opens (PrimeSpectrum.Top R))))
