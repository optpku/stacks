/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Tail.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimit transport for tails of directed ring direct limits

This leaf transports a chosen full-colimit identification across the canonical
tail equivalence.  It is separate from the core comparison and representation
properties so consumers that already have a target colimit need only this
small layer.
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit

namespace Tail

variable {I : Type u} [Preorder I]
variable {G : I → Type v} [∀ i, CommRing (G i)]

/-- Composing the tail-to-full equivalence with a chosen full-colimit
identification gives the corresponding tail-colimit identification. -/
@[stacks 00QV "direct-limit tail"]
noncomputable def equivTo [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I)
    {B : Type w} [CommRing B]
    (colimitIso : Ring.DirectLimit G (fun i j h ↦ f i j h) ≃+* B) :
    Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1)
        (fun j k h ↦ f j.1 k.1 h) ≃+* B :=
  (equiv f i0).trans colimitIso

/-- The tail-colimit identification is `colimitIso` after the canonical map
back to the full direct limit. -/
@[simp, stacks 00QV "direct-limit tail"]
theorem equivTo_apply [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I)
    {B : Type w} [CommRing B]
    (colimitIso : Ring.DirectLimit G (fun i j h ↦ f i j h) ≃+* B)
    (x : Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1)
      (fun j k h ↦ f j.1 k.1 h)) :
    equivTo f i0 colimitIso x = colimitIso (toFull f i0 x) := sorry

/-- The inverse tail-colimit identification sends a full-stage generator to
the same generator in the corresponding tail stage. -/
@[simp, stacks 00QV "direct-limit tail"]
theorem equivTo_symm_apply_of [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I)
    {B : Type w} [CommRing B]
    (colimitIso : Ring.DirectLimit G (fun i j h ↦ f i j h) ≃+* B)
    (j : Set.Ici i0) (x : G j.1) :
    (equivTo f i0 colimitIso).symm
        (colimitIso (Ring.DirectLimit.of G (fun i j h ↦ f i j h) j.1 x)) =
      Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ G j.1)
        (fun j k h ↦ f j.1 k.1 h) j x := sorry

end Tail

end Ring.DirectLimit
