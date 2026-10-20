/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.Smooth.Adic.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness from Adic Formal Smoothness

@stack 07NP
-/

@[expose] public section

open IsLocalRing

universe u v

namespace RingHom

/-- Lemma 15.40.3 (07NP): a local homomorphism of Noetherian local rings that is formally smooth
for the maximal-ideal-adic topology is flat. -/
@[stacks 07NP "maximal-ideal-adic formal smoothness implies flatness"]
theorem flat_of_formallySmooth_for_maximalIdeal_adic
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f]
    (hfs : f.formally_smooth_for_adic (maximalIdeal B)) :
    f.Flat := sorry

end RingHom
