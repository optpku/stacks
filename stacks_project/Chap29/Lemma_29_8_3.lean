module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.QuasiCompactGenericPoint
import StacksCheckRecall

/-!
# Lemma 29.8.3

A quasi-compact morphism is dominant exactly when its image contains the generic point of every
irreducible component of the target.

@stack 01RL
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

#check (AlgebraicGeometry.forall_genericPointOfComponent_mem_range_iff_genericPoints_subset_range :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    (∀ Z : irreducibleComponents S,
      (genericPoints.ofComponent Z : S) ∈ Set.range f.base) ↔
        genericPoints S ⊆ Set.range f.base)

#check (AlgebraicGeometry.isDominant_iff_genericPoints_subset_range :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f],
    IsDominant f ↔ genericPoints S ⊆ Set.range f.base)

/- Lemma 29.8.3: A quasi-compact morphism is dominant if and only if its image contains the
generic point of every irreducible component of the target. -/
@[stacks 01RL] #check
  (AlgebraicGeometry.isDominant_iff_forall_genericPointOfComponent_mem_range :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f],
      IsDominant f ↔
        ∀ Z : irreducibleComponents S,
          (genericPoints.ofComponent Z : S) ∈ Set.range f.base)
