module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace
public import ReasLib.Topology.Stratification.Good
public import ReasLib.Topology.Stratification.Initial

/-!
# Finite refinements by stratifications
-/

@[expose] public section

universe u v

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

namespace LocallyClosedPartition

/-- `Q` is a finite good refinement of the locally closed partition `P`: it has finitely many
parts, refines `P`, and satisfies the frontier condition. -/
@[stacks 09Y5 "finite good locally closed refinement"]
structure IsFiniteGoodRefinement (Q P : LocallyClosedPartition X) : Prop where
  /-- The refining partition has finitely many parts. -/
  finite : Q.toSet.Finite
  /-- The refining partition refines the given partition. -/
  refines : Q.Refines P
  /-- The refining partition satisfies the frontier condition. -/
  isGood : Q.IsGood

/-- The three defining conditions of a finite good refinement. -/
theorem isFiniteGoodRefinement_iff (Q P : LocallyClosedPartition X) :
    Q.IsFiniteGoodRefinement P ↔ Q.toSet.Finite ∧ Q.Refines P ∧ Q.IsGood :=
  ⟨fun h ↦ ⟨h.finite, h.refines, h.isGood⟩, fun ⟨hfinite, hrefines, hgood⟩ ↦
    ⟨hfinite, hrefines, hgood⟩⟩

/-- A finite locally closed partition admits a refinement by a finite indexed stratification. -/
@[stacks 09Y3 "finite stratification refining a locally closed partition"]
theorem exists_finite_stratification_refining (P : LocallyClosedPartition X)
    (hPfinite : P.toSet.Finite) :
    ∃ S : FiniteStratification.{u, 0} X, S.toLocallyClosedPartition.Refines P := sorry

end LocallyClosedPartition

namespace FiniteStratification

/-- A finite constructible cover admits a finite constructible stratification subordinate to that
cover. -/
@[stacks 09Y4 "finite constructible stratification subordinate to a cover"]
theorem exists_constructible_subordinate_to_cover
    {ι : Type v} [Finite ι] (T : ι → Set X)
    (hT : ∀ k, IsConstructible (T k)) (hcover : (univ : Set X) = ⋃ k, T k) :
    ∃ S : FiniteStratification.{u, 0} X,
      (∀ i, IsConstructible (S.strata i)) ∧
        ∀ k, T k = ⋃ i ∈ {j | S.strata j ⊆ T k}, S.strata i := sorry

end FiniteStratification

namespace LocallyClosedPartition

/-- A finite partition of a Noetherian space into locally closed parts admits a finite good
locally closed refinement. -/
@[stacks 09Y5 "finite good refinement in a Noetherian space"]
theorem exists_finite_good_refinement [NoetherianSpace X]
    (P : LocallyClosedPartition X) (hPfinite : P.toSet.Finite) :
    ∃ Q : LocallyClosedPartition X, Q.IsFiniteGoodRefinement P := sorry

end LocallyClosedPartition
