/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Compactness.Basic
import StacksCheckRecall

@[expose] public section

universe u

/-
Mathlib's `CompactSpace` is deliberately separation-free, so it matches the Stacks meaning of
quasi-compactness; `isCompact_iff_finite_subcover` gives the stated open-cover presentation.
-/

/- Definition 111.6.4: a topological space `X` is quasi-compact exactly in the canonical,
separation-free sense `CompactSpace`; equivalently, every open cover of `X` has a finite subcover. -/
@[stacks 027B]
#check (TopologicalSpace.IsQuasiCompact : (X : Type u) → [TopologicalSpace X] → Prop)

/- Companion: the space-level class is equivalent to compactness of `Set.univ`. -/
#check (isCompact_univ_iff : ∀ {X : Type u} [TopologicalSpace X],
  IsCompact (Set.univ : Set X) ↔ CompactSpace X)

/- Companion: the source covering formulation is the canonical finite-subcover characterization of
`IsCompact`. -/
#check (isCompact_iff_finite_subcover : ∀ {X : Type u} [TopologicalSpace X] {s : Set X},
  IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set X),
    (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i)
