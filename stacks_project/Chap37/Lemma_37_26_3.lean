/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GeometricallyReducedFiber

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.26.3: if the generic fibre of a finite-type morphism to an irreducible
scheme is not geometrically reduced, then all fibres over some nonempty open subset
are not geometrically reduced. -/
@[stacks 0577] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_not_geometricallyReduced_fiber :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [IrreducibleSpace Y],
      (¬ AlgebraicGeometry.GeometricallyReduced
        (f.fiberToSpecResidueField (genericPoint Y))) →
        ∃ V : Y.Opens, Nonempty V ∧
          ∀ y : Y, y ∈ V →
            ¬ AlgebraicGeometry.GeometricallyReduced (f.fiberToSpecResidueField y))
