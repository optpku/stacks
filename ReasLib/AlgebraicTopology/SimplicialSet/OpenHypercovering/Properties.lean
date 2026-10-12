/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Definition

/-!
# Pointwise properties of open hypercoverings

The predicates in this module record conditions on all opens or all index types of an open
hypercovering.  They are independent of any basis, sheaf, or cohomology application.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace SSet
namespace OpenHypercovering

variable {X : Type u} [TopologicalSpace X]

/-- A predicate on opens holds degreewise when it holds for every indexed simplex. -/
@[stacks 01H1 "degreewise predicate on an open hypercovering"]
def degreewise (H : OpenHypercovering.{u, v} X) (P : Opens X → Prop) : Prop :=
  ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.I.obj Δ), P (H.family.openAt i)

/-- A degreewise predicate holds for a chosen indexed simplex. -/
@[stacks 01H1 "degreewise predicate at an indexed open"]
theorem degreewise.openAt
    {H : OpenHypercovering.{u, v} X} {P : Opens X → Prop}
    (hH : H.degreewise P) {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    P (H.family.openAt i) := sorry

/-- An open hypercovering is degreewise nonempty when every indexed open is nonempty. -/
@[stacks 01H5 "degreewise nonempty condition"]
def degreewiseNonempty (H : OpenHypercovering.{u, v} X) : Prop :=
  H.degreewise fun U ↦ (U : Set X).Nonempty

/-- Every indexed open of a degreewise nonempty hypercovering is nonempty. -/
@[stacks 01H5 "degreewise nonempty indexed open"]
theorem degreewiseNonempty.openAt_nonempty
    {H : OpenHypercovering.{u, v} X} (hH : H.degreewiseNonempty)
    {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    (H.family.openAt i : Set X).Nonempty := sorry

/-- An indexed open is nonempty exactly when it is not the bottom open. -/
@[stacks 01H5 "open nonempty iff non-bottom"]
theorem openAt_nonempty_iff_ne_bot
    (H : OpenHypercovering.{u, v} X) {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    (H.family.openAt i : Set X).Nonempty ↔ H.family.openAt i ≠ ⊥ := sorry

/-- Degreewise nonemptiness can be checked by asking that every indexed open is non-bottom. -/
@[stacks 01H5 "degreewise nonempty iff degreewise non-bottom"]
theorem degreewiseNonempty_iff_ne_bot (H : OpenHypercovering.{u, v} X) :
    H.degreewiseNonempty ↔
      ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.I.obj Δ), H.family.openAt i ≠ ⊥ := sorry

/-- Every indexed open of a degreewise nonempty hypercovering is non-bottom. -/
@[stacks 01H5 "degreewise non-bottom indexed open"]
theorem degreewiseNonempty.openAt_ne_bot
    {H : OpenHypercovering.{u, v} X} (hH : H.degreewiseNonempty)
    {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    H.family.openAt i ≠ ⊥ := sorry

/-- An open hypercovering lies degreewise in `B` when all of its indexed opens belong to `B`. -/
@[stacks 01H6 "degreewise basis-membership condition"]
def degreewiseOpensIn (H : OpenHypercovering.{u, v} X) (B : Set (Opens X)) : Prop :=
  H.degreewise fun U ↦ U ∈ B

/-- Unfolding `degreewiseOpensIn` quantifies over every indexed simplex. -/
@[stacks 01H6 "degreewise basis membership specification"]
theorem degreewiseOpensIn.iff_forall_simplex
    (H : OpenHypercovering.{u, v} X) (B : Set (Opens X)) :
    H.degreewiseOpensIn B ↔
      ∀ ⦃Δ : SimplexCategoryᵒᵖ⦄ (i : H.I.obj Δ), H.family.openAt i ∈ B := sorry

/-- Every indexed open of a hypercovering lying degreewise in `B` belongs to `B`. -/
@[stacks 01H6 "degreewise basis membership at an indexed open"]
theorem degreewiseOpensIn.openAt_mem
    {H : OpenHypercovering.{u, v} X} {B : Set (Opens X)}
    (hH : H.degreewiseOpensIn B) {Δ : SimplexCategoryᵒᵖ} (i : H.I.obj Δ) :
    H.family.openAt i ∈ B := sorry

/-- An open hypercovering is degreewise finite when each standard simplicial degree has a finite
index type. -/
@[stacks 01H7 "degreewise finite index condition"]
def degreewiseFinite (H : OpenHypercovering.{u, v} X) : Prop :=
  ∀ n : ℕ, Finite (H.I.obj (op <| SimplexCategory.mk n))

/-- The index type in a chosen simplicial degree of a degreewise finite hypercovering is finite. -/
@[stacks 01H7 "finite index type in each degree"]
theorem degreewiseFinite.finite
    {H : OpenHypercovering.{u, v} X} (hH : H.degreewiseFinite) (n : ℕ) :
    Finite (H.I.obj (op <| SimplexCategory.mk n)) := sorry

/-- The degree-`0` index type of a degreewise finite hypercovering is finite. -/
@[stacks 01H7 "finite degree-zero index type"]
theorem degreewiseFinite.zero
    {H : OpenHypercovering.{u, v} X} (hH : H.degreewiseFinite) :
    Finite (H.I.obj (op <| SimplexCategory.mk 0)) := sorry

/-- The degree-`1` index type of a degreewise finite hypercovering is finite. -/
@[stacks 01H7 "finite degree-one index type"]
theorem degreewiseFinite.one
    {H : OpenHypercovering.{u, v} X} (hH : H.degreewiseFinite) :
    Finite (H.I.obj (op <| SimplexCategory.mk 1)) := sorry

/-- The degree-`n + 1` index type of a degreewise finite hypercovering is finite. -/
@[stacks 01H7 "finite successor index type"]
theorem degreewiseFinite.succ
    {H : OpenHypercovering.{u, v} X} (hH : H.degreewiseFinite) (n : ℕ) :
    Finite (H.I.obj (op <| SimplexCategory.mk (n + 1))) := sorry

/-- Every matching family in a degreewise finite open hypercovering is indexed by a finite type.
Together with `H.succ n`, this says that each successor matching cover is finite. -/
@[stacks 01H7 "finite matching-cover indices"]
theorem degreewiseFinite.matchingIndices
    {H : OpenHypercovering.{u, v} X} (hH : H.degreewiseFinite)
    (n : ℕ) (i : Fin (n + 2) → H.I.obj (op <| SimplexCategory.mk n)) :
    Finite (MatchingIndices
      (fun a j ↦ H.I.map (SimplexCategory.δ a).op j) i) := sorry

end OpenHypercovering
end SSet
