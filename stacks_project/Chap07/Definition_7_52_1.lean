/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Topology
import StacksCheckRecall

@[expose]
public section

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Definition 7.52.1: A point of a topology is a set-valued functor such that
covering-sieve stalk maps are surjective and its stalk functor on sheaves is
exact. Initial smallness supplies the formal size condition for these stalks. -/
@[stacks 00ZT] #check (CategoryTheory.GrothendieckTopology.PointOfTopology.{u, v, w} :
  GrothendieckTopology C → Type (max (max u v) (w + 1)))

#check (CategoryTheory.GrothendieckTopology.PointOfTopology.fiber :
  GrothendieckTopology.PointOfTopology.{u, v, w} J → C ⥤ Type w)

#check (CategoryTheory.GrothendieckTopology.PointOfTopology.initiallySmall :
  ∀ p : GrothendieckTopology.PointOfTopology.{u, v, w} J,
    InitiallySmall.{w} p.fiber.Elements)

#check (CategoryTheory.GrothendieckTopology.PointOfTopology.jointly_surjective :
  ∀ (p : GrothendieckTopology.PointOfTopology.{u, v, w} J) {X : C}
    (R : Sieve X), R ∈ J X → ∀ x : p.fiber.obj X,
      ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : p.fiber.obj Y), p.fiber.map f y = x)

#check (CategoryTheory.GrothendieckTopology.PointOfTopology.stalk_exact :
  ∀ p : GrothendieckTopology.PointOfTopology.{u, v, w} J,
    exactFunctor (Sheaf J (Type w)) (Type w)
      (CategoryTheory.GrothendieckTopology.topologyStalk J p.fiber p.initiallySmall))

#check (CategoryTheory.GrothendieckTopology.PointOfTopology.sheafFiber :
  GrothendieckTopology.PointOfTopology.{u, v, w} J → (Sheaf J (Type w) ⥤ Type w))
