/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.Algebra.Category.ModuleCat.FlatResolution
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module Tor dimension after flat scalar extension

@stack 066M

Flat scalar extension preserves the length of a finite flat resolution.  The module-level
Tor-dimension theorem is exposed separately from its resolution presentation so downstream code
can use either layer without rebuilding a chosen resolution in a chapter file.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B]

/-- A finite flat resolution remains a finite flat resolution of the same length after extension
along a flat ring homomorphism. -/
@[stacks 066M "finite flat resolutions after flat scalar extension"]
theorem HasFiniteFlatResolutionLengthLE.extendScalars
    (f : A →+* B) (hf : f.Flat) {M : ModuleCat A} {d : ℕ}
    (hM : HasFiniteFlatResolutionLengthLE M d) :
    HasFiniteFlatResolutionLengthLE ((ModuleCat.extendScalars f).obj M) d := sorry
/- Proof strategy: extend every term and differential of the finite resolution along `f`;
flatness of `f` preserves exactness, while scalar extension carries flat modules to flat
modules and leaves the length bound unchanged. -/

/-- Lemma 15.67.14 (Stacks `066M`): scalar extension along a flat ring homomorphism preserves a
module Tor-dimension bound. -/
@[stacks 066M "module Tor dimension after flat scalar extension"]
theorem HasTorDimensionLE.extendScalars
    (f : A →+* B) (hf : f.Flat) {M : ModuleCat A} {d : ℕ}
    (hM : HasTorDimensionLE (R := A) M d) :
    HasTorDimensionLE (R := B) ((ModuleCat.extendScalars f).obj M) d := sorry
/- Proof strategy: convert `hM` to a finite flat resolution, apply
`HasFiniteFlatResolutionLengthLE.extendScalars`, and convert the resulting resolution back to
the Tor-dimension predicate. -/

end CategoryTheory.ModuleCat
