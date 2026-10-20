/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GeometricallyConnectedFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.28.4: if a finite-type morphism to an irreducible scheme has geometrically
connected generic fibre, then its restriction over some nonempty open subscheme has
geometrically connected fibres. -/
@[stacks 055G] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_geometricallyConnected :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
      [GeometricallyConnected (f.fiberToSpecResidueField (genericPoint Y))],
      ∃ V : Y.Opens, Nonempty V ∧ GeometricallyConnected (f ∣_ V))

end AlgebraicGeometry.Scheme.Hom
