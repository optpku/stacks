/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Topology.Order
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

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

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` has discrete field
fibers if for every field-valued point `y` of `Y` and every bilimit 2-fibre
product cone of `f` against `y.hom`, the space of points of the apex is
discrete for every canonical topology. -/
def discreteFieldFibers {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ (y : FieldValuedPoint Y) (c : PseudoPullbackCone f y.hom)
    [AlgebraicStack c.pt], c.IsBilimit →
    ∀ (τ : TopologicalSpace (Points c.pt)),
      IsPointsTopology c.pt τ → @DiscreteTopology (Points c.pt) τ

/-- Discrete field fibers means every unpackaged morphism `Spec(k) ⟶ Y` from a
field has discrete space of points on every bilimit 2-fibre. -/
theorem discreteFieldFibers_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    discreteFieldFibers f ↔
      ∀ (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S)
        (g : GroupoidsOver.slice (Over.mk σ) ⟶ Y)
        (c : PseudoPullbackCone f g) [AlgebraicStack c.pt],
        c.IsBilimit → ∀ (τ : TopologicalSpace (Points c.pt)),
          IsPointsTopology c.pt τ → @DiscreteTopology (Points c.pt) τ :=
  sorry

namespace discreteFieldFibers

/-- `discreteFieldFibers` implies that every bilimit 2-fibre against a
field-valued point has discrete space of points for every canonical
topology. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : discreteFieldFibers f) (y : FieldValuedPoint Y)
    (c : PseudoPullbackCone f y.hom) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    (τ : TopologicalSpace (Points c.pt)) (hτ : IsPointsTopology c.pt τ) :
    @DiscreteTopology (Points c.pt) τ :=
  sorry

end discreteFieldFibers

/-- A morphism `f : X ⟶ Y` of algebraic stacks over `S` is locally
quasi-finite if it is quasi-DM, locally of finite type, and has discrete
field fibers. -/
@[mk_iff]
class LocallyQuasiFinite {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends QuasiDM f, LocallyOfFiniteType f where
  /-- Every field-valued 2-fibre of `f` has discrete space of points. -/
  fieldFibersDiscrete : discreteFieldFibers f

namespace LocallyQuasiFinite

/-- The identity morphism of an algebraic stack is locally quasi-finite. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    LocallyQuasiFinite (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic stacks is locally quasi-finite. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] :
    LocallyQuasiFinite f :=
  sorry

/-- A morphism of algebraic spaces that is locally quasi-finite and locally of
finite type induces a locally quasi-finite morphism of algebraic stacks. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyQuasiFinite f]
    [AlgebraicSpace.LocallyOfFiniteType f] :
    LocallyQuasiFinite (AlgebraicSpace.toGroupoids.map f) :=
  sorry

/-- A locally quasi-finite morphism of algebraic stacks is quasi-DM, locally
of finite type, and has discrete field fibers. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyQuasiFinite f] :
    QuasiDM f ∧ LocallyOfFiniteType f ∧ discreteFieldFibers f :=
  sorry

/-- The chosen 2-fibre product of a locally quasi-finite morphism against a
field-valued point has discrete space of points for every canonical
topology, once the apex is known to be an algebraic stack. -/
theorem twoFibreProduct_discrete {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} [LocallyQuasiFinite f]
    (y : FieldValuedPoint Y)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f y.hom)]
    (τ : TopologicalSpace
      (Points (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f y.hom)))
    (hτ : IsPointsTopology
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f y.hom) τ) :
    @DiscreteTopology
      (Points (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f y.hom)) τ :=
  sorry

end LocallyQuasiFinite

end AlgebraicGeometry.AlgebraicStack
