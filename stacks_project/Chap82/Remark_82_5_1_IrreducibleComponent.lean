/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sober
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.IrreducibleComponent

/-!
# Irreducible components of closed subspaces

The component constructions and their specifications are provided by the shared
mathematical owners. These checks preserve the component API for chapter consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.genericPoints_eq_canonical :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    genericPoints X = _root_.genericPoints (Points X))

#check (_root_.genericPoints.equiv :
  ∀ {α : Type u} [TopologicalSpace α] [T0Space α] [QuasiSober α],
    _root_.genericPoints α ≃ irreducibleComponents α)

#check (_root_.genericPoints.isGenericPoint_ofComponent :
  ∀ {α : Type u} [TopologicalSpace α] [QuasiSober α]
    (T : irreducibleComponents α),
    IsGenericPoint (_root_.genericPoints.ofComponent T).1 (T : Set α))

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.instIsQuasiSeparated :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiSeparated X] (Y : ClosedSubspace X),
    IsQuasiSeparated Y.X)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.instIsDecent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (Y : ClosedSubspace X),
    IsDecent Y.X)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.IsIrreducibleComponent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) (Z : ClosedSubspace Y.X),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.isIrreducibleComponent_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) (Z : ClosedSubspace Y.X),
    IsIrreducibleComponent Y Z ↔
      IsIntegral Z.X ∧ Z.pointsSet ∈ irreducibleComponents (Points Y.X))

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.irreducibleComponent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X),
    ClosedSubspace Y.X)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.irreducibleComponent_spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X),
    IsIntegral (irreducibleComponent Y η).X ∧
      IsIrreducibleComponent Y (irreducibleComponent Y η))

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.pointsSet_irreducibleComponent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X),
    (irreducibleComponent Y η).pointsSet = closure {η.1})

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.genericPoint :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y : ClosedSubspace X} [IsDecent Y.X] (Z : ClosedSubspace Y.X)
    [IsIntegral Z.X],
    Points Y.X)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.isGenericPoint_genericPoint :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y : ClosedSubspace X} [IsDecent Y.X] (Z : ClosedSubspace Y.X)
    [IsIntegral Z.X],
    IsGenericPoint (genericPoint Z) Z.pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.mem_genericPoints_genericPoint :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y : ClosedSubspace X} [IsDecent Y.X] (Z : ClosedSubspace Y.X)
    [IsIntegral Z.X] (hZ : IsIrreducibleComponent Y Z),
    genericPoint Z ∈ genericPoints Y.X)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.existsUnique_hom_irreducibleComponent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X)
    (Z' : ClosedSubspace Y.X) [IsIntegral Z'.X]
    (h : Z'.pointsSet = (irreducibleComponent Y η).pointsSet),
    ∃! g : Z'.X ⟶ (irreducibleComponent Y η).X,
      g ≫ (irreducibleComponent Y η).ι = Z'.ι)
