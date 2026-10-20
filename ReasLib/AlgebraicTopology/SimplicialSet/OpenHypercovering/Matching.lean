module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Lattice
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.SimplicialSet.Tuple
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Matching indices for simplicial hypercoverings

This module owns the finite tuple of face conditions that defines a matching index.  It is purely
combinatorial and has no topological hypotheses.
-/

@[expose] public section

open CategoryTheory Opposite

universe v w

namespace SSet

namespace OpenHypercovering

variable {n : ℕ} {In : Type v} {In1 : Type w}

namespace Boundary

/-- The canonical compatible boundary-tuple type attached to a simplicial index set. -/
@[stacks 01H1 "compatible boundary tuple"]
abbrev Tuple (I : SSet.{v}) {n : ℕ} :=
  CategoryTheory.SimplicialObject.Truncated.matching.FaceFamily.Tuple
    ((SSet.truncation n).obj I)

/-- Compatibility of a proposed simplicial boundary, using the canonical matching-tuple
predicate for the truncation of the index simplicial set. -/
@[stacks 01H1 "compatible boundary of an open hypercovering"]
abbrev Compatible (I : SSet.{v}) {n : ℕ}
    (face : Fin (n + 2) → I.obj (op <| SimplexCategory.mk n)) : Prop :=
  CategoryTheory.SimplicialObject.Truncated.matching.FaceFamily.Tuple.Compatible
    ((SSet.truncation n).obj I) face

namespace Compatible

/-- Every pair of vertices is a compatible degree-zero boundary. -/
@[simp]
theorem zero (I : SSet.{v})
    (face : Fin 2 → I.obj (op <| SimplexCategory.mk 0)) :
    Boundary.Compatible I face := sorry

/-- In positive degree, boundary compatibility is exactly the pairwise simplicial face
relation appearing in the hypercovering condition. -/
@[simp, stacks 01H3 "positive-degree open-hypercovering boundary compatibility"]
theorem succ_iff (I : SSet.{v}) {m : ℕ}
    (face : Fin (m + 3) → I.obj (op <| SimplexCategory.mk (m + 1))) :
    Boundary.Compatible I face ↔
      ∀ i j : Fin (m + 2), i ≤ j →
        I.δ j (face i.castSucc) = I.δ i (face j.succ) := sorry

end Compatible

end Boundary

/-- The level-`n + 1` indices whose faces agree with a prescribed family of level-`n` indices. -/
@[stacks 01H4 "matching indices for a finite intersection"]
abbrev MatchingIndices
    (d : Fin (n + 2) → In1 → In) (i : Fin (n + 2) → In) :=
  { j : In1 // ∀ a : Fin (n + 2), d a j = i a }

namespace MatchingIndices

/-- The faces of a simplex form a compatible boundary.  This bridge lets hypercovering
intersection APIs recover compatibility directly from a matching filler index. -/
@[stacks 01H1 "matching indices have compatible boundaries"]
theorem compatible {I : SSet.{v}} {n : ℕ}
    {face : Fin (n + 2) → I.obj (op <| SimplexCategory.mk n)}
    (j : MatchingIndices (fun a x ↦ I.δ a x) face) :
    Boundary.Compatible I face := sorry

/-- The `a`th face of a matching index is the prescribed level-`n` index. -/
@[stacks 01H4 "matching index face equation"]
theorem face_eq
    {d : Fin (n + 2) → In1 → In} {i : Fin (n + 2) → In}
    (j : MatchingIndices d i) (a : Fin (n + 2)) :
    d a j = i a := sorry

/-- A two-face matching index satisfies the corresponding pair of equations. -/
theorem finTwoToFun_mem {I0 : Type v} {I1 : Type w}
    (d0 d1 : I1 → I0) (i0 i1 : I0)
    (j : MatchingIndices ![d0, d1] ![i0, i1]) :
    d0 j.1 = i0 ∧ d1 j.1 = i1 := sorry

/-- Forget the tuple presentation of a two-face matching index. -/
def finTwoToFun {I0 : Type v} {I1 : Type w}
    (d0 d1 : I1 → I0) (i0 i1 : I0) :
    MatchingIndices ![d0, d1] ![i0, i1] →
      { j : I1 // d0 j = i0 ∧ d1 j = i1 } :=
  fun j ↦ ⟨j.1, finTwoToFun_mem d0 d1 i0 i1 j⟩

/-- A pair of face equations satisfies the tuple presentation of the matching condition. -/
theorem finTwoInvFun_mem {I0 : Type v} {I1 : Type w}
    (d0 d1 : I1 → I0) (i0 i1 : I0)
    (j : { j : I1 // d0 j = i0 ∧ d1 j = i1 }) :
    ∀ a : Fin 2, ![d0, d1] a j.1 = ![i0, i1] a := sorry

/-- Regard a pair of face equations as a two-face matching index. -/
def finTwoInvFun {I0 : Type v} {I1 : Type w}
    (d0 d1 : I1 → I0) (i0 i1 : I0) :
    { j : I1 // d0 j = i0 ∧ d1 j = i1 } →
      MatchingIndices ![d0, d1] ![i0, i1] :=
  fun j ↦ ⟨j.1, finTwoInvFun_mem d0 d1 i0 i1 j⟩

/-- Converting a two-face matching index to paired equations and back is the identity. -/
theorem finTwo_leftInverse {I0 : Type v} {I1 : Type w}
    (d0 d1 : I1 → I0) (i0 i1 : I0)
    (j : MatchingIndices ![d0, d1] ![i0, i1]) :
    finTwoInvFun d0 d1 i0 i1 (finTwoToFun d0 d1 i0 i1 j) = j := sorry

/-- Converting paired face equations to a matching index and back is the identity. -/
theorem finTwo_rightInverse {I0 : Type v} {I1 : Type w}
    (d0 d1 : I1 → I0) (i0 i1 : I0)
    (j : { j : I1 // d0 j = i0 ∧ d1 j = i1 }) :
    finTwoToFun d0 d1 i0 i1 (finTwoInvFun d0 d1 i0 i1 j) = j := sorry

/-- Two-face matching indices are canonically equivalent to the pairwise matching subtype. -/
@[stacks 01H3 "two-face matching indices"]
def finTwoEquiv {I0 : Type v} {I1 : Type w}
    (d0 d1 : I1 → I0) (i0 i1 : I0) :
    MatchingIndices ![d0, d1] ![i0, i1] ≃ { j : I1 // d0 j = i0 ∧ d1 j = i1 } where
  toFun := finTwoToFun d0 d1 i0 i1
  invFun := finTwoInvFun d0 d1 i0 i1
  left_inv := finTwo_leftInverse d0 d1 i0 i1
  right_inv := finTwo_rightInverse d0 d1 i0 i1

namespace finTwoEquiv

/-- The forward two-face matching equivalence preserves the underlying index. -/
@[simp] theorem val {I0 : Type v} {I1 : Type w}
    (d0 d1 : I1 → I0) (i0 i1 : I0)
    (j : MatchingIndices ![d0, d1] ![i0, i1]) :
    (SSet.OpenHypercovering.MatchingIndices.finTwoEquiv d0 d1 i0 i1 j).1 = j.1 := sorry

/-- The inverse two-face matching equivalence preserves the underlying index. -/
@[simp] theorem symm_val {I0 : Type v} {I1 : Type w}
    (d0 d1 : I1 → I0) (i0 i1 : I0)
    (j : { j : I1 // d0 j = i0 ∧ d1 j = i1 }) :
    ((SSet.OpenHypercovering.MatchingIndices.finTwoEquiv d0 d1 i0 i1).symm j).1 = j.1 := sorry

end finTwoEquiv

end MatchingIndices
end OpenHypercovering
end SSet
