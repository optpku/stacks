/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DMLocus
import StacksCheckRecall

/-!
# Points of the DM and quasi-DM loci

A field-valued point of an algebraic stack lies in the DM locus exactly when
its automorphism group algebraic space is unramified over the ground field, and
in the quasi-DM locus exactly when that group space is locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

/- Lemma 101.22.2 (1): A field-valued point lies in the DM locus exactly when
its automorphism group is unramified over its source field. -/
@[stacks 0DSN]
#check (AlgebraicGeometry.AlgebraicStack.memDMLocus_iff_unramified :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (p : FieldValuedPoint X),
    memDMLocus (Points.mk p) ↔
      automorphismGroup.Has (@AlgebraicSpace.Unramified S) p)

/- Lemma 101.22.2 (2): A field-valued point lies in the quasi-DM locus exactly
when its automorphism group is locally quasi-finite over its source field. -/
@[stacks 0DSN]
#check (AlgebraicGeometry.AlgebraicStack.memQuasiDMLocus_iff_locallyQuasiFinite :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (p : FieldValuedPoint X),
    memQuasiDMLocus (Points.mk p) ↔
      automorphismGroup.Has (@AlgebraicSpace.LocallyQuasiFinite S) p)
