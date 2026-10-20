/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.Basic
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/- Definition 61.7.1: a ring map `A → B` is ind-étale if `B` can be written as
a filtered colimit of étale `A`-algebras. Canonical owner: `RingHom.IndEtale`. -/
@[stacks 097I] #check (RingHom.IndEtale : (R →+* A) → Prop)

#check RingHom.IndEtale.Raw
#check RingHom.IndEtale.ofRaw
#check RingHom.IndEtale.ofEtale
