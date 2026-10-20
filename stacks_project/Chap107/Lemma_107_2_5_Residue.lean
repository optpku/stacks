/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Restriction
public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.ResidueExtension
public import stacks_project.Chap98.«98_3_0_1_Factorization»
public import stacks_project.Chap98.Definition_98_9_1_AlgebraHom

/-! # Residue-field restriction of field-valued points -/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.restrict :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    (l : Type u) [Field l] [Algebra x0.K l],
    AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.restrictFactorization :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    (l : Type u) [Field l] [Algebra x0.K l],
    AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Factorization (x0.restrict l) x0)

#check (AlgebraicGeometry.CompleteLocalSAlgebra.Hom.InducesResidueExtension :
  ∀ {S : Scheme.{u}} {A A' : CompleteLocalSAlgebra S}
    (φ : CompleteLocalSAlgebra.Hom A' A)
    (k l : Type u) [Field k] [Field l] [Algebra k l]
    (σk : Spec (.of k) ⟶ S) (σl : Spec (.of l) ⟶ S), Prop)
