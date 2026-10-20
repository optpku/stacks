/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.Composition
import StacksCheckRecall

universe u v w

@[expose] public section

/- Lemma 61.7.3: if ring maps `A → B` and `B → C` are ind-étale, then the
composite `A → C` is ind-étale. Canonical owner: `RingHom.IndEtale.comp`. -/
@[stacks 097K] #check (RingHom.IndEtale.comp : ∀ {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
  f.IndEtale → g.IndEtale → (g.comp f).IndEtale)
