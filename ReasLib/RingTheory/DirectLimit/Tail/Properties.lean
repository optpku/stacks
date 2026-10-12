/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Tail.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Representation properties for tails of directed ring direct limits

This leaf records stage-representation and common-stage existence results.  It
depends only on the canonical comparison layer and does not own a particular
identification of the full direct limit with another colimit.
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit

namespace Tail

variable {I : Type u} [Preorder I]
variable {G : I → Type v} [∀ i, CommRing (G i)]

/-- The inverse comparison sends any original stage representative to a
representative at some stage of the prescribed tail.  The existential form
keeps the noncanonical upper-bound choice internal to the construction. -/
@[stacks 00QV "direct-limit tail"]
theorem exists_fromFull_of [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 i : I) (x : G i) :
    ∃ (j : Set.Ici i0) (hij : i ≤ j.1),
      fromFull f i0
          (Ring.DirectLimit.of G (fun i j h ↦ f i j h) i x) =
        Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ G j.1)
          (fun j k h ↦ f j.1 k.1 h) j (f i j.1 hij x) := sorry

/-- Every element of a full directed direct limit is represented by a stage in
the tail above `i0`.  This existential form deliberately hides the
noncanonical common-upper-bound choice used by `fromFull`. -/
@[stacks 00QV "direct-limit tail"]
theorem exists_of [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I)
    (z : Ring.DirectLimit G (fun i j h ↦ f i j h)) :
    ∃ (j : Set.Ici i0) (x : G j.1),
      Ring.DirectLimit.of G (fun i j h ↦ f i j h) j.1 x = z := sorry

/-- A finite family of elements of a full directed direct limit is represented
at one common stage of any prescribed tail. -/
@[stacks 00QV "direct-limit tail"]
theorem exists_common_of_finset [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ f i j h)] (i0 : I)
    {K : Type w} (s : Finset K)
    (z : K → Ring.DirectLimit G (fun i j h ↦ f i j h)) :
    ∃ (j : Set.Ici i0) (x : K → G j.1), ∀ k ∈ s,
      Ring.DirectLimit.of G (fun i j h ↦ f i j h) j.1 (x k) = z k := sorry

end Tail

end Ring.DirectLimit
