module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.GenericPoint
import StacksCheckRecall

/-!
# Lemma 29.8.2

A morphism is dominant if its image contains every generic point of every irreducible component
of the target.

@stack 01RK
-/

@[expose] public section

universe u

#check @AlgebraicGeometry.Scheme.Hom.genericPointOfComponent_mem_range
#check @AlgebraicGeometry.mem_closure_range_of_mem_irreducibleComponent
#check @AlgebraicGeometry.isDominant_of_forall_genericPointOfComponent_mem_range

/- Lemma 29.8.2: If every generic point of every irreducible component of the target of a
scheme morphism lies in its image, then the morphism is dominant. -/
@[stacks 01RK] #check
  (AlgebraicGeometry.isDominant_of_genericPoint_mem_range_of_irreducibleComponents :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      (∀ Z : irreducibleComponents S, ∀ ⦃s : S⦄,
        IsGenericPoint s (Z : Set S) → s ∈ Set.range f.base) →
      AlgebraicGeometry.IsDominant f)
