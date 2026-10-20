/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.EssentialFiniteness.BaseChange
public import ReasLib.RingTheory.EssentialFiniteness.Presentation

/-!
# Ring-Homomorphism API for Essential Finite Presentation

This module exposes composition and base-change stability in the canonical
`RingHom.EssFinitePresentation` namespace.
-/

@[expose] public section

universe u v w

namespace RingHom.EssFinitePresentation

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]

/-- Composition of essentially finitely presented ring homomorphisms is essentially finitely
presented. -/
theorem comp {f : R →+* S} {g : S →+* T} (hf : f.EssFinitePresentation)
    (hg : g.EssFinitePresentation) : (g.comp f).EssFinitePresentation := sorry

/-- Essential finite presentation is stable under composition of ring homomorphisms. -/
theorem stableUnderComposition : RingHom.StableUnderComposition RingHom.EssFinitePresentation := sorry

/-- Essential finite presentation is stable under base change of ring homomorphisms. -/
theorem isStableUnderBaseChange : RingHom.IsStableUnderBaseChange RingHom.EssFinitePresentation := sorry

end RingHom.EssFinitePresentation
