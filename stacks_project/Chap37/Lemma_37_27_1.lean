module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.IrreducibleComponents

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/-
Lemma 37.27.1: over some nonempty open subset of an irreducible base, the fibres of a
finite-type morphism have at least as many irreducible components as the generic fibre.
-/
@[stacks 0554] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_le_natCard_irreducibleComponents :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Scheme.Hom.FiniteType f]
      [IrreducibleSpace Y] {n : ℕ},
      Nat.card (irreducibleComponents (f.fiber (genericPoint Y))) = n →
        ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V →
          n ≤ Nat.card (irreducibleComponents (f.fiber y)))
