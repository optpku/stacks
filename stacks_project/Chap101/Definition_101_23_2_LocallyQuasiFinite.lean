/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Topology.Order
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

/-!
# Locally quasi-finite morphisms of algebraic stacks

A morphism of algebraic stacks is locally quasi-finite when it is quasi-DM,
locally of finite type, and every field-valued 2-fibre has discrete space of
points. Competing topologies on `Points` remain explicit parameters.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.discreteFieldFibers :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicStack.discreteFieldFibers_iff :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    discreteFieldFibers f ↔
      ∀ (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S)
        (g : GroupoidsOver.slice (Over.mk σ) ⟶ Y)
        (c : PseudoPullbackCone f g) [AlgebraicStack c.pt],
        c.IsBilimit → ∀ (τ : TopologicalSpace (Points c.pt)),
          IsPointsTopology c.pt τ → @DiscreteTopology (Points c.pt) τ)

#check (AlgebraicGeometry.AlgebraicStack.discreteFieldFibers.spec :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : discreteFieldFibers f) (y : FieldValuedPoint Y)
    (c : PseudoPullbackCone f y.hom) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (τ : TopologicalSpace (Points c.pt)) (hτ : IsPointsTopology c.pt τ),
    @DiscreteTopology (Points c.pt) τ)

#check (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.id :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    LocallyQuasiFinite (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.of_isIso :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f],
    LocallyQuasiFinite f)

#check (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.of_toGroupoids :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyQuasiFinite f]
    [AlgebraicSpace.LocallyOfFiniteType f],
    LocallyQuasiFinite (AlgebraicSpace.toGroupoids.map f))

#check (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.spec :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyQuasiFinite f],
    QuasiDM f ∧ LocallyOfFiniteType f ∧ discreteFieldFibers f)

#check (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.twoFibreProduct_discrete :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [LocallyQuasiFinite f]
    (y : FieldValuedPoint Y)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f y.hom)]
    (τ : TopologicalSpace
      (Points (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f y.hom)))
    (hτ : IsPointsTopology
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f y.hom) τ),
    @DiscreteTopology
      (Points (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f y.hom)) τ)

end AlgebraicGeometry.AlgebraicStack
