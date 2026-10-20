/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.RingTheory.Normal.Local
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Global sections of punctured spectra

The regular functions on the punctured spectrum of a Noetherian normal local ring of dimension
at least two are determined by the ring.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A]

/-- For a Noetherian normal local ring of Krull dimension at least two, the canonical algebra map
to the global sections on its punctured spectrum is bijective. -/
theorem algebraMap_puncturedOpen_bijective (hdim : 2 ≤ ringKrullDim A) :
    Function.Bijective
      (algebraMap A
        ((Spec.structureSheaf A).obj.obj (Opposite.op (puncturedOpen A)) : Type u)) := sorry

end AlgebraicGeometry.PuncturedSpectrum
