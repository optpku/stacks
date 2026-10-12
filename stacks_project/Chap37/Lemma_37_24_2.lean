/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GenericFiber

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.24.2: a finite-type morphism to an irreducible scheme with nonempty generic
fiber is surjective after restriction to some nonempty open subscheme of the target. -/
@[stacks 05F5]
#check (AlgebraicGeometry.Scheme.Hom.FiniteType.exists_open_surjective :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] [IrreducibleSpace Y],
    Nonempty (f.fiber (genericPoint Y)) →
      ∃ V : Y.Opens, Nonempty V ∧ AlgebraicGeometry.Surjective (f ∣_ V))
