/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Integral
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sober
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap68.Lemma_68_12_3
public import stacks_project.Chap68.Proposition_68_12_4
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Points, irreducible closed subsets, and integral closed subspaces

On a decent algebraic space, the sober space of points is in bijection with
irreducible closed subsets via singleton closures. Each irreducible closed
subset carries a canonical integral closed subspace, namely its reduced
induced structure, recovered uniquely up to a morphism over the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The space of points of a decent algebraic space is in bijection with its
irreducible closed subsets. -/
noncomputable def pointsEquivIrreducibleCloseds {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] : Points X ≃ IrreducibleCloseds (Points X) :=
  irreducibleSetEquivPoints.toEquiv.symm

/-- The bijection from points of a decent algebraic space to irreducible closed
subsets sends a point `x` to the closure of `{x}`. -/
theorem coe_pointsEquivIrreducibleCloseds {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) :
    (pointsEquivIrreducibleCloseds X x : Set (Points X)) = closure {x} :=
  coe_irreducibleEquivPoints_symm_apply x

/-- The inverse of `pointsEquivIrreducibleCloseds` sends an irreducible closed
subset to its generic point. -/
theorem isGenericPoint_pointsEquivIrreducibleCloseds_symm {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    IsGenericPoint ((pointsEquivIrreducibleCloseds X).symm T) (T : Set (Points X)) :=
  T.isIrreducible.isGenericPoint_genericPoint T.isClosed

#check (ClosedSubspace.ofIrreducibleClosed :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → [IsDecent X] →
    IrreducibleCloseds (Points X) → ClosedSubspace X)

#check (ReducedClosed.Space.instIsIntegral_irreducibleClosed :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (T : IrreducibleCloseds (Points X)),
    IsIntegral (ReducedClosed.Space.space X (Closeds.mk (T : Set (Points X)) T.isClosed)))

#check (ClosedSubspace.pointsSet_ofIrreducibleClosed :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (T : IrreducibleCloseds (Points X)),
    (ClosedSubspace.ofIrreducibleClosed T).pointsSet = (T : Set (Points X)))

#check (ClosedSubspace.ofIrreducibleClosed_spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (T : IrreducibleCloseds (Points X)),
    IsIntegral (ClosedSubspace.ofIrreducibleClosed T).X ∧
      (ClosedSubspace.ofIrreducibleClosed T).pointsSet = (T : Set (Points X)))

#check (ClosedSubspace.isIrreducible_pointsSet :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) [IsIntegral Z.X],
    _root_.IsIrreducible Z.pointsSet)

#check (ClosedSubspace.irreducibleClosed :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → (Z : ClosedSubspace X) →
    [IsIntegral Z.X] → IrreducibleCloseds (Points X))

#check (ClosedSubspace.coe_irreducibleClosed :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) [IsIntegral Z.X],
    (Z.irreducibleClosed : Set (Points X)) = Z.pointsSet)

#check (ClosedSubspace.existsUnique_hom_ofIrreducibleClosed :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (Z : ClosedSubspace X) [IsIntegral Z.X],
    ∃! f : Z.X ⟶ (ClosedSubspace.ofIrreducibleClosed Z.irreducibleClosed).X,
      f ≫ (ClosedSubspace.ofIrreducibleClosed Z.irreducibleClosed).ι = Z.ι)

end AlgebraicGeometry.AlgebraicSpace
