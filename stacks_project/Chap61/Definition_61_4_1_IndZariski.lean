/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski

@[expose] public section

/-!
# Ind-Zariski ring homomorphisms

The ind-Zariski predicate and its transport API are provided by
`ReasLib.RingTheory.RingHom.IndZariski`.
-/

universe u v

#check CommRingCat.localIso
#check CommRingCat.localIso_iff
#check CommRingCat.localIso_respectsIso
#check (@RingHom.IndZariski :
  ∀ {R : Type u} {A : Type v} [CommRing R] [CommRing A], (R →+* A) → Prop)
#check RingHom.IndZariski.Raw
#check RingHom.IndZariski.ofRaw
#check RingHom.IndZariski.ofIsLocalIso
#check RingHom.IndZariski.Raw.ofIsLocalIso
#check RingHom.IndZariski.Raw.algebraMap_iff
#check RingHom.IndZariski.Raw.of_ind
