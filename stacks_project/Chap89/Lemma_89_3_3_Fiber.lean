/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Fiber

/-!
# Comparison of field-valued fibres of morphisms of algebraic spaces

Commutative squares and factorizations of field-valued points induce the
canonical fibre comparison maps supplied by ReasLib.  Their composite compares
the residue-field fibre after base change along a scheme point with the fibre
over an explicitly given field-valued point of the target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.fiberOver_mapSquare :
  ∀ {S : Scheme.{u}} {Y Y' V W : AlgebraicSpace S}
    (f : Y ⟶ W) (a : V ⟶ W) (fst : Y' ⟶ Y) (g : Y' ⟶ V)
    (p : FieldValuedPoint V), fst ≫ f = g ≫ a →
      (fieldFiber g p ⟶ fieldFiber f (p.map a)))

#check (AlgebraicGeometry.AlgebraicSpace.fiberOver_mapSquare_spec :
  ∀ {S : Scheme.{u}} {Y Y' V W : AlgebraicSpace S}
    (f : Y ⟶ W) (a : V ⟶ W) (fst : Y' ⟶ Y) (g : Y' ⟶ V)
    (p : FieldValuedPoint V) (hw : fst ≫ f = g ≫ a),
    fiberOver_mapSquare f a fst g p hw ≫ fieldFiberι f (p.map a) =
        fieldFiberι g p ≫ fst ∧
      fiberOver_mapSquare f a fst g p hw ≫ fieldFiberToSpec f (p.map a) =
        fieldFiberToSpec g p)

#check (AlgebraicGeometry.AlgebraicSpace.fiberOver_factor :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    {p q : FieldValuedPoint X}, p.Factorization q → (fieldFiber f p ⟶ fieldFiber f q))

#check (AlgebraicGeometry.AlgebraicSpace.fiberOver_factor_spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    {p q : FieldValuedPoint X} (φ : p.Factorization q),
    fiberOver_factor f φ ≫ fieldFiberι f q = fieldFiberι f p ∧
      fiberOver_factor f φ ≫ fieldFiberToSpec f q =
        fieldFiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure)

#check (AlgebraicGeometry.AlgebraicSpace.fiberOver_neighborhoodComparison :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) {V : Over S}
    (a : ofOver V ⟶ X) (v : V.left) {q : FieldValuedPoint X},
    ((FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)).map a).Factorization q →
      (fieldFiber (overPullbackSnd a (Over.mk f))
          (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint v)) ⟶
        fieldFiber f q))
