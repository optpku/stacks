/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import ReasLib.RingTheory.RingHom.IndEtale.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal etaleness of ind-etale maps

An ind-etale map is a filtered colimit of etale maps, hence formally etale.

@stack 07QN
-/

@[expose] public section

universe u v

namespace RingHom.IndEtale

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- An ind-etale ring homomorphism is formally etale. -/
@[stacks 07QN "ind-etale maps are formally etale"]
theorem formallyEtale (f : R →+* S) (hf : f.IndEtale) : f.FormallyEtale := sorry

end RingHom.IndEtale
