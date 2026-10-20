module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Dominant.FiniteComponents
import StacksCheckRecall

/-!
# Lemma 29.8.7

Dominance from a source with finitely many irreducible components is detected on component
generic points, and forces the target to have finitely many irreducible components.

@stack 01RM
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 29.8.7 (1): A morphism from a scheme with finitely many irreducible components is
dominant if and only if its image contains the generic point of every irreducible component of
the target. -/
@[stacks 01RM] #check
  (@AlgebraicGeometry.IsDominant.iff_genericPointOfComponent_mem_range :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Finite (irreducibleComponents X)],
      IsDominant f ↔ ∀ Z : irreducibleComponents S,
        (genericPoints.ofComponent Z : S) ∈ Set.range f.base)

/- Lemma 29.8.7 (2): If a dominant morphism has source with finitely many irreducible
components, then its target also has finitely many irreducible components. -/
@[stacks 01RM] #check
  (@AlgebraicGeometry.finite_irreducibleComponents_target_of_isDominant :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Finite (irreducibleComponents X)] [IsDominant f],
      Finite (irreducibleComponents S))
