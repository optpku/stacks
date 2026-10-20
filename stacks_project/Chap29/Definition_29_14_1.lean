/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.RingTheory.LocalProperties.Basic
import StacksCheckRecall

universe u

/- Definition 29.14.1 (1): locality for a property of commutative-ring maps. -/
@[stacks 01SR] #check (RingHom.PropertyIsLocal :
  ({R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop) → Prop)

/- Definition 29.14.1 (2): stability under base change for a property of
commutative-ring maps. -/
@[stacks 01SR] #check (RingHom.IsStableUnderBaseChange :
  ({R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop) → Prop)

/- Definition 29.14.1 (3): stability under composition for a property of
commutative-ring maps. -/
@[stacks 01SR] #check (RingHom.StableUnderComposition :
  ({R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop) → Prop)
