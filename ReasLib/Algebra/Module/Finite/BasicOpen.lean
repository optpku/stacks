/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Finiteness
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation

@[expose] public section

universe u v w

open PrimeSpectrum
open scoped PrimeSpectrum

/-- Finite generation of a module can be detected on a basic-open cover of the prime spectrum. -/
theorem Module.Finite.of_basicOpen_cover
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type w} (f : ι → A) (hcover : (⨆ i, D(f i)) = ⊤)
    (h : ∀ i, Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) :
    Module.Finite A M := sorry
