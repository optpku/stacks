module

public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.Core
public import ReasLib.RingTheory.DirectLimit.Tail
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tail direct-limit algebra and equivalences

This leaf owns the algebra structures on a tail direct limit, its canonical
stage maps, and the algebra equivalence with the full direct limit.
-/

@[expose] public section

universe u v

noncomputable section

namespace Ring.DirectLimit.Algebra.Tail

variable {I : Type u} [Preorder I]
variable {A : I → Type v} [∀ i, CommRing (A i)]

/-- The direct limit of the tail is canonically an algebra over the tail base
stage, using the base tail stage `⟨i0, le_rfl⟩`. -/
@[reducible, stacks 00QV "direct-limit algebra tail"]
noncomputable def directLimitAlgebra
    (f : ∀ i j, i ≤ j → A i →+* A j) (i0 : I) :
    Algebra (A i0)
      (Ring.DirectLimit (fun j : Set.Ici i0 ↦ A j.1)
        (fun j k h ↦ f j.1 k.1 h)) :=
  (Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ A j.1)
    (fun j k h ↦ f j.1 k.1 h) ⟨i0, le_rfl⟩).toAlgebra

/-- The scalar map of the tail direct-limit algebra is its canonical map from
the base tail stage. -/
@[stacks 00QV "direct-limit algebra tail"]
theorem directLimitAlgebra_algebraMap
    (f : ∀ i j, i ≤ j → A i →+* A j) (i0 : I) :
    letI : Algebra (A i0)
      (Ring.DirectLimit (fun j : Set.Ici i0 ↦ A j.1)
        (fun j k h ↦ f j.1 k.1 h)) := directLimitAlgebra f i0
    algebraMap (A i0)
      (Ring.DirectLimit (fun j : Set.Ici i0 ↦ A j.1)
        (fun j k h ↦ f j.1 k.1 h)) =
      Ring.DirectLimit.of (fun j : Set.Ici i0 ↦ A j.1)
        (fun j k h ↦ f j.1 k.1 h) ⟨i0, le_rfl⟩ := sorry

/-- The canonical map from a tail stage into its tail direct limit, as an
algebra homomorphism over the tail base stage. -/
@[stacks 00QV "direct-limit algebra tail"]
noncomputable def of
    (f : ∀ i j, i ≤ j → A i →+* A j)
    (i0 : I) (j : Set.Ici i0) :
    letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
    letI : Algebra (A i0)
      (Ring.DirectLimit (fun k : Set.Ici i0 ↦ A k.1)
        (fun k l h ↦ f k.1 l.1 h)) := directLimitAlgebra f i0
    A j.1 →ₐ[A i0]
      Ring.DirectLimit (fun k : Set.Ici i0 ↦ A k.1)
        (fun k l h ↦ f k.1 l.1 h) :=
  letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
  letI : Algebra (A i0)
    (Ring.DirectLimit (fun k : Set.Ici i0 ↦ A k.1)
      (fun k l h ↦ f k.1 l.1 h)) := directLimitAlgebra f i0
  { toRingHom := Ring.DirectLimit.of (fun k : Set.Ici i0 ↦ A k.1)
      (fun k l h ↦ f k.1 l.1 h) j
    commutes' := sorry }

/-- The tail-stage algebra map evaluates through the underlying direct-limit
stage map. -/
@[simp, stacks 00QV "direct-limit algebra tail"]
theorem of_apply
    (f : ∀ i j, i ≤ j → A i →+* A j)
    (i0 : I) (j : Set.Ici i0) (x : A j.1) :
    of f i0 j x =
      Ring.DirectLimit.of (fun k : Set.Ici i0 ↦ A k.1)
        (fun k l h ↦ f k.1 l.1 h) j x := sorry

/-- The canonical map from a tail stage into the full direct limit, as an
algebra homomorphism over the tail base stage. -/
@[stacks 00QV "direct-limit algebra tail"]
noncomputable def ofFull
    (f : ∀ i j, i ≤ j → A i →+* A j)
    (i0 : I) (j : Set.Ici i0) :
    letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
    letI : Algebra (A i0)
      (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
    A j.1 →ₐ[A i0] Ring.DirectLimit A (fun i j h ↦ f i j h) :=
  letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
  letI : Algebra (A i0)
    (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
      Ring.DirectLimit.Algebra.stageAlgebra f i0
  { toRingHom := Ring.DirectLimit.of A (fun i j h ↦ f i j h) j.1
    commutes' := sorry }

/-- The full-limit algebra map from a tail stage evaluates through the
underlying full direct-limit stage map. -/
@[simp, stacks 00QV "direct-limit algebra tail"]
theorem ofFull_apply
    (f : ∀ i j, i ≤ j → A i →+* A j)
    (i0 : I) (j : Set.Ici i0) (x : A j.1) :
    ofFull f i0 j x = Ring.DirectLimit.of A (fun i j h ↦ f i j h) j.1 x := sorry

/-- The canonical tail-stage map respects transitions inside the tail. -/
@[stacks 00QV "direct-limit algebra tail"]
theorem of_comp_transition
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)]
    (i0 : I) {j k : Set.Ici i0} (hjk : j ≤ k) :
    letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
    letI : Algebra (A i0) (A k.1) := stageAlgebra f i0 k
    letI : Algebra (A i0)
      (Ring.DirectLimit (fun l : Set.Ici i0 ↦ A l.1)
        (fun l m h ↦ f l.1 m.1 h)) := directLimitAlgebra f i0
    (of f i0 k).comp (transition f i0 hjk) = of f i0 j := sorry

/-- The canonical tail-stage map into the full direct limit respects tail
transitions. -/
@[stacks 00QV "direct-limit algebra tail"]
theorem ofFull_comp_transition
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)]
    (i0 : I) {j k : Set.Ici i0} (hjk : j ≤ k) :
    letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
    letI : Algebra (A i0) (A k.1) := stageAlgebra f i0 k
    letI : Algebra (A i0)
      (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
    (ofFull f i0 k).comp (transition f i0 hjk) = ofFull f i0 j := sorry

/-- The tail direct limit is canonically equivalent to the full direct limit
as an algebra over its tail base stage. -/
@[stacks 00QV "direct-limit algebra tail"]
noncomputable def equiv [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I) :
    letI : Algebra (A i0)
      (Ring.DirectLimit (fun j : Set.Ici i0 ↦ A j.1)
        (fun j k h ↦ f j.1 k.1 h)) := directLimitAlgebra f i0
    letI : Algebra (A i0)
      (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
    Ring.DirectLimit (fun j : Set.Ici i0 ↦ A j.1)
      (fun j k h ↦ f j.1 k.1 h) ≃ₐ[A i0]
      Ring.DirectLimit A (fun i j h ↦ f i j h) :=
  letI : Algebra (A i0)
    (Ring.DirectLimit (fun j : Set.Ici i0 ↦ A j.1)
      (fun j k h ↦ f j.1 k.1 h)) := directLimitAlgebra f i0
  letI : Algebra (A i0)
    (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
      Ring.DirectLimit.Algebra.stageAlgebra f i0
  { __ := Ring.DirectLimit.Tail.equiv f i0
    commutes' := sorry }

/-- The algebra tail/full equivalence has the underlying forward map of the
corresponding ring tail/full equivalence. -/
@[simp, stacks 00QV "direct-limit algebra tail"]
theorem equiv_apply [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I)
    (x : Ring.DirectLimit (fun j : Set.Ici i0 ↦ A j.1)
      (fun j k h ↦ f j.1 k.1 h)) :
    equiv f i0 x = Ring.DirectLimit.Tail.toFull f i0 x := sorry

/-- The tail/full algebra equivalence sends a tail-stage class to the same
class in the full direct limit. -/
@[stacks 00QV "direct-limit algebra tail"]
theorem equiv_of [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I)
    (j : Set.Ici i0) (x : A j.1) :
    letI : Algebra (A i0)
      (Ring.DirectLimit (fun k : Set.Ici i0 ↦ A k.1)
        (fun k l h ↦ f k.1 l.1 h)) := directLimitAlgebra f i0
    letI : Algebra (A i0)
      (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
    equiv f i0
        (Ring.DirectLimit.of (fun k : Set.Ici i0 ↦ A k.1)
          (fun k l h ↦ f k.1 l.1 h) j x) =
      Ring.DirectLimit.of A (fun i j h ↦ f i j h) j.1 x := sorry

/-- The inverse algebra tail/full equivalence sends a full generator from the
tail to the corresponding tail generator. -/
@[simp, stacks 00QV "direct-limit algebra tail"]
theorem equiv_symm_of [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I)
    (j : Set.Ici i0) (x : A j.1) :
    letI : Algebra (A i0)
      (Ring.DirectLimit (fun k : Set.Ici i0 ↦ A k.1)
        (fun k l h ↦ f k.1 l.1 h)) := directLimitAlgebra f i0
    letI : Algebra (A i0)
      (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
    (equiv f i0).symm
        (Ring.DirectLimit.of A (fun i j h ↦ f i j h) j.1 x) =
      Ring.DirectLimit.of (fun k : Set.Ici i0 ↦ A k.1)
        (fun k l h ↦ f k.1 l.1 h) j x := sorry

/-- The tail/full algebra equivalence intertwines the canonical stage maps. -/
@[stacks 00QV "direct-limit algebra tail"]
theorem equiv_comp_of [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I)
    (j : Set.Ici i0) :
    letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
    letI : Algebra (A i0)
      (Ring.DirectLimit (fun k : Set.Ici i0 ↦ A k.1)
        (fun k l h ↦ f k.1 l.1 h)) := directLimitAlgebra f i0
    letI : Algebra (A i0)
      (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
    (equiv f i0).toAlgHom.comp (of f i0 j) = ofFull f i0 j := sorry

/-- Applying the inverse tail/full algebra equivalence after a full stage map
recovers the canonical map from that stage into the tail direct limit. -/
@[stacks 00QV "direct-limit algebra tail"]
theorem equiv_symm_comp_ofFull [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I)
    (j : Set.Ici i0) :
    letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
    letI : Algebra (A i0)
      (Ring.DirectLimit (fun k : Set.Ici i0 ↦ A k.1)
        (fun k l h ↦ f k.1 l.1 h)) := directLimitAlgebra f i0
    letI : Algebra (A i0)
      (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
    ((equiv f i0).symm.toAlgHom).comp (ofFull f i0 j) = of f i0 j := sorry

end Ring.DirectLimit.Algebra.Tail
