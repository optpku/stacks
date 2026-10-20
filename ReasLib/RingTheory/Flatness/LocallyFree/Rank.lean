/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite

/-!
# Rank Criteria for Finite Local Freeness

This leaf owns the rank-at-stalk interface for `Module.FiniteLocallyFree`.
Natural-valued rank is canonical; the integer-valued statements are thin
source-compatible companions for the formulation used in Chapter 10.
-/

@[expose] public section

universe u v

namespace Module

namespace FiniteLocallyFree

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Tag `00NX`: stalk rank is locally constant for a finite locally free module. -/
@[stacks 00NX "stalk rank of a finite locally free module"]
theorem isLocallyConstant_rankAtStalk (h : FiniteLocallyFree R M) :
    IsLocallyConstant (fun p : PrimeSpectrum R ↦ rankAtStalk M p) := sorry

/-- Tag `00NX`: the integer-valued stalk rank is locally constant for a finite locally free
module. -/
@[stacks 00NX "integer stalk rank of a finite locally free module"]
theorem isLocallyConstant_intRankAtStalk (h : FiniteLocallyFree R M) :
    IsLocallyConstant (fun p : PrimeSpectrum R ↦ (rankAtStalk M p : ℤ)) := sorry

/-- Tag `00NX`: a finite module with free stalks and locally constant natural-number stalk rank
is finite locally free. -/
@[stacks 00NX "finite local freeness from free stalks and rank"]
theorem of_freeLocus_eq_univ_of_isLocallyConstant_rankAtStalk
    (hfinite : Module.Finite R M) (hfree : freeLocus R M = Set.univ)
    (hrank : IsLocallyConstant (fun p : PrimeSpectrum R ↦ rankAtStalk M p)) :
    FiniteLocallyFree R M := sorry

/-- Tag `00NX`: an integer-valued locally constant stalk rank, together with finite generation
and free stalks, constructs finite local freeness. -/
@[stacks 00NX "finite local freeness from integer stalk rank"]
theorem of_freeLocus_eq_univ_of_isLocallyConstant_intRankAtStalk
    (hfinite : Module.Finite R M) (hfree : freeLocus R M = Set.univ)
    (hrank : IsLocallyConstant (fun p : PrimeSpectrum R ↦ (rankAtStalk M p : ℤ))) :
    FiniteLocallyFree R M := sorry

end FiniteLocallyFree

end Module
