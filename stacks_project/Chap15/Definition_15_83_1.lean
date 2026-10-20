/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Perfect.TorDimension
import StacksCheckRecall

/-!
# Definition 15.83.1

@stack 067H
-/

@[expose] public section

universe u v

/-!
# Definition 15.83.1 compatibility entry point

The intrinsic pseudo-coherent and perfect commutative ring-map predicates are
owned by `ReasLib.RingTheory.RingHom.PseudoCoherent.Basic` and
`ReasLib.RingTheory.RingHom.Perfect.Basic`.
-/

/- Definition 15.83.1 (1), tag `067H`: pseudo-coherent ring maps. -/
@[stacks 067H "Definition 15.83.1 (1), pseudo-coherent ring map"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) =>
  (f.IsPseudoCoherentRingMap : Prop)

/- Definition 15.83.1 (2), tag `067H`: perfect ring maps. -/
@[stacks 067H "Definition 15.83.1 (2), perfect ring map"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) =>
  (f.IsPerfectRingMap : Prop)

/- The source formulation of perfectness as pseudo-coherence plus finite Tor dimension. -/
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) =>
  (RingHom.isPerfectRingMap_iff_isPseudoCoherentRingMap_and_hasFiniteTorDimension f :
    f.IsPerfectRingMap ↔ f.IsPseudoCoherentRingMap ∧ f.HasFiniteTorDimension)
