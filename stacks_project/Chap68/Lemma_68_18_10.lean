/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.QuasiFinite

/-!
# Conditions on fibres and quasi-finiteness

These six clauses record the implication diagram for a locally finite-type
morphism of algebraic spaces and a field-valued representative of the target point.
They compare finite and discrete fibres, the two dimension notions, and
quasi-finiteness at all points of the set-theoretic fibre. Decency supplies the
additional implications and equivalences.

The source writes dimension equal to zero. Here zero-dimensionality means
dimension at most zero, so that empty fibres are included: their dimensions
are bottom (the source's dimension of the empty space is minus infinity).
No nonemptiness hypothesis is imposed. The finite-field-fibre implication is
valid for arbitrary morphisms, without a finite-type hypothesis.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.18.10. Conditions (5), (6), (7), and (8) are equivalent. -/
@[stacks 0ACK] #check (AlgebraicGeometry.AlgebraicSpace.tfae_fieldFiber_discrete_dimension_quasiFiniteAt :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y),
    List.TFAE
      [ DiscreteTopology (Points (fieldFiber f p))
      , topologicalKrullDim (Points (fieldFiber f p)) ≤ 0
      , dimension (fieldFiber f p) ≤ 0
      , ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x ])

/- Finite field-valued fibres give finite set-theoretic fibres: (4) implies (1). -/
#check (AlgebraicGeometry.AlgebraicSpace.finite_fiberOver_of_finite_fieldFiber :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) (hXk : Finite (Points (fieldFiber f p))),
    (fiberOver f (Points.mk p)).Finite)

/- For a decent morphism, (4) implies (5). -/
#check (AlgebraicGeometry.AlgebraicSpace.discreteTopology_fieldFiber_of_decent_finite :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [Decent f]
    (p : FieldValuedPoint Y) [Finite (Points (fieldFiber f p))],
    DiscreteTopology (Points (fieldFiber f p)))

/- For a decent target, (2), (3), (5), (6), (7), and (8) are equivalent. -/
#check (AlgebraicGeometry.AlgebraicSpace.tfae_fiberOver_of_isDecent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent Y] (p : FieldValuedPoint Y),
    List.TFAE
      [ DiscreteTopology (fiberOver f (Points.mk p))
      , topologicalKrullDim (fiberOver f (Points.mk p)) ≤ 0
      , DiscreteTopology (Points (fieldFiber f p))
      , topologicalKrullDim (Points (fieldFiber f p)) ≤ 0
      , dimension (fieldFiber f p) ≤ 0
      , ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x ])

/- For decent source and target, (1) implies (8), hence (2), (3), and (5)–(8). -/
#check (AlgebraicGeometry.AlgebraicSpace.quasiFiniteAt_fiberOver_of_isDecent_finite :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y)
    (hF : (fiberOver f (Points.mk p)).Finite),
    ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x)

/- For decent source and target, (1) also implies (4). -/
#check (AlgebraicGeometry.AlgebraicSpace.finite_fieldFiber_of_isDecent_finite :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y)
    [Finite (fiberOver f (Points.mk p))],
    Finite (Points (fieldFiber f p)))
