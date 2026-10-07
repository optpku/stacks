module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.GenericPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.GenericPointAvoidance
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dominance of quasi-compact morphisms from generic points

For a quasi-compact scheme morphism, dominance is equivalent to containing the generic point of
every irreducible component of the target.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The componentwise canonical-generic-point criterion is equivalent to containment of the set
of all generic points of the target. -/
theorem forall_genericPointOfComponent_mem_range_iff_genericPoints_subset_range
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (∀ Z : irreducibleComponents S, (genericPoints.ofComponent Z : S) ∈ Set.range f.base) ↔
      genericPoints S ⊆ Set.range f.base := by
  constructor
  · intro h s hs
    simpa using h (genericPoints.equiv ⟨s, hs⟩)
  · intro h Z
    exact h (genericPoints.ofComponent Z).2

/-- A quasi-compact scheme morphism is dominant exactly when its image contains every generic
point of the target. -/
@[stacks 01RL]
theorem isDominant_iff_genericPoints_subset_range {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] :
    IsDominant f ↔ genericPoints S ⊆ Set.range f.base := by
  rw [← forall_genericPointOfComponent_mem_range_iff_genericPoints_subset_range]
  constructor
  · intro hf Z
    by_contra hη
    rcases exists_open_preimage_eq_bot_of_genericPoint_not_mem_range f
        (genericPoints.isGenericPoint_ofComponent Z) hη with ⟨V, hηV, hpre⟩
    have hdense : DenseRange f.base := (isDominant_iff f).mp hf
    rcases hdense.mem_nhds (V.2.mem_nhds hηV) with ⟨x, hx⟩
    have hx' : x ∈ (f ⁻¹ᵁ V : Set X) := hx
    have hempty : x ∈ (∅ : Set X) := by
      simpa only [hpre, TopologicalSpace.Opens.coe_bot] using hx'
    exact (Set.mem_empty_iff_false x).mp hempty
  · exact isDominant_of_forall_genericPointOfComponent_mem_range f

/-- A quasi-compact scheme morphism is dominant exactly when its image contains the canonical
generic point of every irreducible component of the target. -/
@[stacks 01RL]
theorem isDominant_iff_forall_genericPointOfComponent_mem_range
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] :
    IsDominant f ↔
      ∀ Z : irreducibleComponents S,
        (genericPoints.ofComponent Z : S) ∈ Set.range f.base := by
  exact (isDominant_iff_genericPoints_subset_range f).trans
    (forall_genericPointOfComponent_mem_range_iff_genericPoints_subset_range f).symm

end AlgebraicGeometry
