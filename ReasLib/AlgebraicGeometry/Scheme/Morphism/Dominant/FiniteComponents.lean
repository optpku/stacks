/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.GenericPoint
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dominance and finite irreducible components

This file gives the generic-point criterion for dominance when the source has finitely many
irreducible components, together with the resulting finiteness theorem for the target.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The closure of the range of a map from a space with finitely many irreducible components is
the union of the closures of the images of those components. -/
theorem closure_range_eq_iUnion_closure_image_irreducibleComponents
    {X S : Scheme.{u}} (f : X ⟶ S) [Finite (irreducibleComponents X)] :
    closure (Set.range f.base) =
      ⋃ W : irreducibleComponents X, closure (Set.image f.base (W : Set X)) := by
  apply le_antisymm
  · apply closure_minimal
    · rintro _ ⟨x, rfl⟩
      let W : irreducibleComponents X :=
        ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
      exact Set.mem_iUnion_of_mem W (subset_closure ⟨x, mem_irreducibleComponent, rfl⟩)
    · exact isClosed_iUnion_of_finite fun _ ↦ isClosed_closure
  · rw [Set.iUnion_subset_iff]
    intro W
    apply closure_minimal
    · rintro _ ⟨x, _, rfl⟩
      exact subset_closure ⟨x, rfl⟩
    · exact isClosed_closure

/-- If the generic point of an irreducible component `Z` lies in the closure of the image of an
irreducible component `W`, then that closure is exactly `Z`. -/
theorem closure_image_irreducibleComponent_eq_of_genericPoint_mem
    {X S : Scheme.{u}} (f : X ⟶ S) (W : irreducibleComponents X)
    (Z : irreducibleComponents S)
    (hη : (genericPoints.ofComponent Z : S) ∈
      closure (Set.image f.base (W : Set X))) :
    closure (Set.image f.base (W : Set X)) = (Z : Set S) := by
  have hZsub : (Z : Set S) ⊆ closure (Set.image f.base (W : Set X)) :=
    ((genericPoints.isGenericPoint_ofComponent Z).mem_closed_set_iff isClosed_closure).mp hη
  exact le_antisymm
    (Z.2.2 (W.2.1.image f.base f.continuous.continuousOn).closure hZsub) hZsub

/-- A morphism from a scheme with finitely many irreducible components is dominant if and only if
its image contains the generic point of every irreducible component of the target. -/
@[stacks 01RM]
theorem IsDominant.iff_genericPointOfComponent_mem_range
    {X S : Scheme.{u}} (f : X ⟶ S) [Finite (irreducibleComponents X)] :
    IsDominant f ↔
      ∀ Z : irreducibleComponents S,
        (genericPoints.ofComponent Z : S) ∈ Set.range f.base := by
  constructor
  · intro hf Z
    have hη : (genericPoints.ofComponent Z : S) ∈ closure (Set.range f.base) :=
      (isDominant_iff f).mp hf (genericPoints.ofComponent Z)
    rw [closure_range_eq_iUnion_closure_image_irreducibleComponents f] at hη
    obtain ⟨W, hηW⟩ := Set.mem_iUnion.mp hη
    have hclosure := closure_image_irreducibleComponent_eq_of_genericPoint_mem f W Z hηW
    have hgeneric : IsGenericPoint
        (f (genericPoints.ofComponent W)) (Z : Set S) := by
      rw [← hclosure]
      exact (genericPoints.isGenericPoint_ofComponent W).image f.continuous
    exact ⟨genericPoints.ofComponent W,
      ((genericPoints.isGenericPoint_ofComponent Z).eq hgeneric).symm⟩
  · exact isDominant_of_forall_genericPointOfComponent_mem_range f

/-- If a dominant morphism has source with finitely many irreducible components, then its target
also has finitely many irreducible components. -/
@[stacks 01RM]
theorem finite_irreducibleComponents_target_of_isDominant
    {X S : Scheme.{u}} (f : X ⟶ S) [Finite (irreducibleComponents X)] [IsDominant f] :
    Finite (irreducibleComponents S) := by
  classical
  have hgeneric :=
    (IsDominant.iff_genericPointOfComponent_mem_range f).mp
      (show IsDominant f from inferInstance)
  let preimage (Z : irreducibleComponents S) : X :=
    Classical.choose (hgeneric Z)
  have hpreimage (Z : irreducibleComponents S) :
      f (preimage Z) = (genericPoints.ofComponent Z : S) :=
    Classical.choose_spec (hgeneric Z)
  let component (Z : irreducibleComponents S) : irreducibleComponents X :=
    ⟨irreducibleComponent (preimage Z),
      irreducibleComponent_mem_irreducibleComponents (preimage Z)⟩
  have hclosure (Z : irreducibleComponents S) :
      closure (Set.image f.base (component Z : Set X)) = (Z : Set S) := by
    apply closure_image_irreducibleComponent_eq_of_genericPoint_mem f (component Z) Z
    exact subset_closure ⟨preimage Z, mem_irreducibleComponent, hpreimage Z⟩
  exact Finite.of_injective component fun Z₁ Z₂ hcomponent ↦ by
    apply Subtype.ext
    rw [← hclosure Z₁, ← hclosure Z₂, hcomponent]

end AlgebraicGeometry
