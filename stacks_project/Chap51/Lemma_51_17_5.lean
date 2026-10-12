/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Sequence.Independence
import StacksCheckRecall

@[expose] public section

universe u v

namespace RingTheory.Sequence.IsIndependent

/- Lemma 51.17.5: a flat ring homomorphism sends an independent finite family to an
independent finite family. -/
@[stacks 0EBZ] #check (RingTheory.Sequence.IsIndependent.map_of_flat :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] {n : ℕ} {f : Fin n → A},
    RingTheory.Sequence.IsIndependent f → (φ : A →+* B) → RingHom.Flat φ →
      RingTheory.Sequence.IsIndependent (fun i ↦ φ (f i)))

end RingTheory.Sequence.IsIndependent
