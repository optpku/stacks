/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Order.DirectLimit.Tail
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Core comparisons for tails of directed ring direct limits

This leaf owns the canonical maps between a directed ring direct limit and
the direct limit of a prescribed tail.  The noncanonical common-upper-bound
choice is kept in `Internal`; public users use the comparison maps and their
computation laws.
-/

@[expose] public section

universe u v

noncomputable section

namespace Ring.DirectLimit

namespace Tail

variable {I : Type u} [Preorder I]
variable {G : I → Type v} [∀ i, CommRing (G i)]

namespace Internal

/-- A selected common upper bound, viewed as a stage in the tail above `i0`.
This implementation choice is internal; public users interact through the
canonical direct-limit comparison maps. -/
noncomputable def upperBound [IsDirectedOrder I] (i0 i : I) : Set.Ici i0 :=
  ⟨(exists_ge_ge i i0).choose, (exists_ge_ge i i0).choose_spec.2⟩

/-- The selected tail upper bound lies above the original stage. -/
theorem le_upperBound [IsDirectedOrder I] (i0 i : I) :
    i ≤ (upperBound i0 i).1 := sorry

/-- The map from an arbitrary stage into the direct limit of the tail.  It is
internal because its chosen upper bound is noncanonical. -/
noncomputable def stageToTail [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j) (i0 i : I) :
    G i →+* Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1)
      (fun j k h ↦ f j.1 k.1 h) :=
  (Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ G j.1)
      (fun j k h ↦ f j.1 k.1 h) (upperBound i0 i)).comp
    (f i (upperBound i0 i).1 (le_upperBound i0 i))

/-- The chosen stage-to-tail maps respect the transition maps of the original
directed system. -/
theorem stageToTail_compatible [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)]
    (i0 : I) {i j : I} (hij : i ≤ j) (x : G i) :
    stageToTail f i0 j (f i j hij x) = stageToTail f i0 i x := sorry

end Internal

/-- The canonical map from the direct limit of the tail above `i0` to the
direct limit of the full system. -/
@[stacks 00QV "direct-limit tail"]
noncomputable def toFull
    (f : ∀ i j, i ≤ j → G i →+* G j) (i0 : I) :
    Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1)
        (fun j k h ↦ f j.1 k.1 h) →+*
      Ring.DirectLimit G (fun i j h ↦ f i j h) :=
  Ring.DirectLimit.lift
    (fun j : Set.Ici i0 ↦ G j.1)
    (fun j k h ↦ f j.1 k.1 h)
    (Ring.DirectLimit G (fun i j h ↦ f i j h))
    (fun j ↦ Ring.DirectLimit.of G (fun i j h ↦ f i j h) j.1)
    (fun j k hjk x ↦
      Ring.DirectLimit.of_f
        (G := G) (f := fun i j h ↦ f i j h)
        (i := j.1) (j := k.1) hjk x)

/-- The tail-to-full comparison sends a tail-stage generator to the same
generator in the full direct limit. -/
@[simp, stacks 00QV "direct-limit tail"]
theorem toFull_of
    (f : ∀ i j, i ≤ j → G i →+* G j) (i0 : I)
    (j : Set.Ici i0) (x : G j.1) :
    toFull f i0
        (Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ G j.1)
          (fun j k h ↦ f j.1 k.1 h) j x) =
      Ring.DirectLimit.of G (fun i j h ↦ f i j h) j.1 x := sorry

/-- The canonical map from the full direct limit to the direct limit of the
tail above `i0`. -/
@[stacks 00QV "direct-limit tail"]
noncomputable def fromFull [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I) :
    Ring.DirectLimit G (fun i j h ↦ f i j h) →+*
      Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1)
        (fun j k h ↦ f j.1 k.1 h) :=
  Ring.DirectLimit.lift G (fun i j h ↦ f i j h)
    (Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1)
      (fun j k h ↦ f j.1 k.1 h))
    (fun i ↦ Internal.stageToTail f i0 i)
    (fun _ _ hij x ↦ Internal.stageToTail_compatible f i0 hij x)

/-- The full-to-tail comparison sends a generator already indexed by the tail
to the corresponding tail-stage generator. -/
@[simp, stacks 00QV "direct-limit tail"]
theorem fromFull_of [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I)
    (j : Set.Ici i0) (x : G j.1) :
    fromFull f i0 (Ring.DirectLimit.of G (fun i j h ↦ f i j h) j.1 x) =
      Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ G j.1)
        (fun j k h ↦ f j.1 k.1 h) j x := sorry

/-- Passing from the full direct limit to its tail and back is the identity. -/
@[stacks 00QV "direct-limit tail"]
theorem toFull_comp_fromFull [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I) :
    (toFull f i0).comp (fromFull f i0) = RingHom.id _ := sorry

/-- The tail-to-full comparison followed by the chosen inverse evaluates to the
identity on every element of the full direct limit. -/
@[simp, stacks 00QV "direct-limit tail"]
theorem toFull_comp_fromFull_apply [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I)
    (x : Ring.DirectLimit G (fun i j h ↦ f i j h)) :
    toFull f i0 (fromFull f i0 x) = x := sorry

/-- Passing from the tail direct limit to the full direct limit and back is the
identity. -/
@[stacks 00QV "direct-limit tail"]
theorem fromFull_comp_toFull [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I) :
    (fromFull f i0).comp (toFull f i0) = RingHom.id _ := sorry

/-- The chosen inverse followed by the tail-to-full comparison evaluates to the
identity on every element of the tail direct limit. -/
@[simp, stacks 00QV "direct-limit tail"]
theorem fromFull_comp_toFull_apply [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I)
    (x : Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1)
      (fun j k h ↦ f j.1 k.1 h)) :
    fromFull f i0 (toFull f i0 x) = x := sorry

/-- The direct limit of a directed ring system is canonically equivalent to the
direct limit of the tail above `i0`. -/
@[stacks 00QV "direct-limit tail"]
noncomputable def equiv [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I) :
    Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1)
        (fun j k h ↦ f j.1 k.1 h) ≃+*
      Ring.DirectLimit G (fun i j h ↦ f i j h) :=
  RingEquiv.ofRingHom
    (toFull f i0)
    (fromFull f i0)
    (toFull_comp_fromFull f i0)
    (fromFull_comp_toFull f i0)

/-- The tail direct limit maps to the full direct limit through `toFull`. -/
@[simp, stacks 00QV "direct-limit tail"]
theorem equiv_apply [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I)
    (x : Ring.DirectLimit (fun j : Set.Ici i0 ↦ G j.1)
      (fun j k h ↦ f j.1 k.1 h)) :
    equiv f i0 x = toFull f i0 x := sorry

/-- The inverse tail/full equivalence sends a full generator already indexed by
the tail to the corresponding tail-stage generator. -/
@[simp, stacks 00QV "direct-limit tail"]
theorem equiv_symm_apply_of [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I)
    (j : Set.Ici i0) (x : G j.1) :
    (equiv f i0).symm
        (Ring.DirectLimit.of G (fun i j h ↦ f i j h) j.1 x) =
      Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ G j.1)
        (fun j k h ↦ f j.1 k.1 h) j x := sorry

end Tail

end Ring.DirectLimit
