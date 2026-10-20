/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import ReasLib.RingTheory.Localization.Away.Relative.MapMul
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation after principal localization

@stack 00FG
-/

@[expose] public section

universe u v

namespace Algebra.FiniteType

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S]

/-- Lemma 10.30.1: for a finite-type inclusion into a domain, suitable
nonzero principal localizations make the induced map finitely presented. -/
@[stacks 00FG]
theorem exists_awayMapMul_finitePresentation :
    ∃ (f : R) (_ : f ≠ 0) (g : S) (_ : g ≠ 0),
      (Localization.Away.Relative.mapMul (algebraMap R S) f g).FinitePresentation := sorry

end Algebra.FiniteType
