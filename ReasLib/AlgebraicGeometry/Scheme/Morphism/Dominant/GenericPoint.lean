/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dominance from generic points

This file records a criterion for a scheme morphism to be dominant in terms of the generic
points of the irreducible components of its target.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- If every generic point witness on every irreducible component of `S` lies in the image of `f`,
then the canonical chosen generic point of each irreducible component lies in the image of `f`. -/
theorem Scheme.Hom.genericPointOfComponent_mem_range
    (hgeneric :
      ∀ Z : irreducibleComponents S, ∀ ⦃s : S⦄,
        IsGenericPoint s (Z : Set S) → s ∈ Set.range f.base) :
    ∀ Z : irreducibleComponents S, (genericPoints.ofComponent Z : S) ∈ Set.range f.base :=
  fun Z ↦ hgeneric Z (genericPoints.isGenericPoint_ofComponent Z)

/-- If the canonical generic point of an irreducible component `Z` lies in the image of `f`, then
every point of `Z` lies in the closure of the image of `f`. -/
theorem mem_closure_range_of_mem_irreducibleComponent
    (hgeneric :
      ∀ Z : irreducibleComponents S, (genericPoints.ofComponent Z : S) ∈ Set.range f.base)
    (Z : irreducibleComponents S) {s : S} (hs : s ∈ (Z : Set S)) :
    s ∈ closure (Set.range f.base) := by
  have hη : (genericPoints.ofComponent Z : S) ∈ closure (Set.range f.base) :=
    subset_closure (hgeneric Z)
  exact ((genericPoints.isGenericPoint_ofComponent Z).specializes hs).mem_closed
    isClosed_closure hη

/-- If the canonical generic point of every irreducible component of `S` lies in the image of
`f`, then `f` is dominant. -/
theorem isDominant_of_forall_genericPointOfComponent_mem_range
    (hgeneric :
      ∀ Z : irreducibleComponents S, (genericPoints.ofComponent Z : S) ∈ Set.range f.base) :
    IsDominant f := by
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff]
  intro s _
  rcases exists_mem_irreducibleComponents_subset_of_isIrreducible ({s} : Set S)
      (by simpa using (isIrreducible_singleton : IsIrreducible ({s} : Set S))) with
    ⟨Z, hZ, hsZ⟩
  let Z' : irreducibleComponents S := ⟨Z, hZ⟩
  exact mem_closure_range_of_mem_irreducibleComponent f hgeneric Z'
    (hsZ (Set.mem_singleton s))

/-- If every generic point of every irreducible component of the target scheme lies in the image
of `f`, then `f` is dominant. -/
@[stacks 01RK]
theorem isDominant_of_genericPoint_mem_range_of_irreducibleComponents
    (hgeneric :
      ∀ Z : irreducibleComponents S, ∀ ⦃s : S⦄,
        IsGenericPoint s (Z : Set S) → s ∈ Set.range f.base) :
    IsDominant f :=
  isDominant_of_forall_genericPointOfComponent_mem_range f
    (Scheme.Hom.genericPointOfComponent_mem_range f hgeneric)

end AlgebraicGeometry
