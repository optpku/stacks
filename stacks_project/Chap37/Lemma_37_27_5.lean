/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GeometricallyIrreducibleFiber

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.27.5: if a finite-type morphism to an irreducible scheme has geometrically
irreducible generic fibre, then its restriction over some nonempty open subscheme has
geometrically irreducible fibres. -/
@[stacks 0559]
#check (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_geometricallyIrreducible :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FiniteType f] [IrreducibleSpace Y]
      [GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint Y))],
    ∃ V : Y.Opens, Nonempty V ∧ GeometricallyIrreducible (f ∣_ V))
