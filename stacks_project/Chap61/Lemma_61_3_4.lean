/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Local.Properties
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.3.4 (1): if `S → T` is an `R`-algebra homomorphism and both `R → S`
and `R → T` are local isomorphisms, then `S → T` is a local isomorphism. -/
@[stacks 096H] #check
  (RingHom.IsLocalIso.of_comp :
    {R S T : Type u} → [CommRing R] → [CommRing S] → [CommRing T] →
      {f : R →+* S} → {g : S →+* T} → RingHom.IsLocalIso f →
      RingHom.IsLocalIso (g.comp f) → RingHom.IsLocalIso g)

/- Lemma 61.3.4 (2): if `S → T` is an `R`-algebra homomorphism and both `R → S`
and `R → T` identify local rings, then `S → T` identifies local rings. -/
@[stacks 096H] #check
  (RingHom.IsIsoOnLocalRings.of_comp :
    {R S T : Type u} → [CommRing R] → [CommRing S] → [CommRing T] →
      {f : R →+* S} → {g : S →+* T} → RingHom.IsIsoOnLocalRings f →
      RingHom.IsIsoOnLocalRings (g.comp f) → RingHom.IsIsoOnLocalRings g)
