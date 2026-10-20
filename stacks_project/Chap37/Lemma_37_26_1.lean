module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ReducedFiber

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.26.1: if the generic fibre of a finite-type morphism to an irreducible
scheme is nonreduced, then all fibres over some nonempty open subset are nonreduced. -/
@[stacks 0575] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_not_isReduced_fiber :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [IrreducibleSpace Y],
      (¬ AlgebraicGeometry.IsReduced
        (f.fiber (genericPoint Y))) →
        ∃ V : Y.Opens, Nonempty V ∧
          ∀ y : Y, y ∈ V → ¬ AlgebraicGeometry.IsReduced (f.fiber y))
