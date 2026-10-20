/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- A local ring is pure when finite étale covers of its punctured spectrum
extend essentially surjectively over its spectrum. -/
abbrev HasPurity (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  (Scheme.finiteEtaleBaseChange (puncturedOpen A).ι).EssSurj

/-- Purity is equivalent to extending every finite étale cover of the punctured spectrum. -/
theorem hasPurity_iff
    (A : Type u) [CommRing A] [IsLocalRing A] :
    HasPurity A ↔
      ∀ V : Scheme.FiniteEtale (scheme A),
        ∃ Y : Scheme.FiniteEtale (Spec (CommRingCat.of A)),
          Nonempty ((Scheme.finiteEtaleBaseChange (puncturedOpen A).ι).obj Y ≅ V) := sorry

end AlgebraicGeometry.PuncturedSpectrum
