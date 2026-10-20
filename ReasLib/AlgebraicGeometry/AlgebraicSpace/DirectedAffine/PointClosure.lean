/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.Closure

/-!
# Point closures in directed affine-transition limits of algebraic spaces

The inverse system of reduced closures of the stagewise images of a point of a
limiting cone, and the comparison of that system with the reduced closure of
the limiting point, both as sets and as algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (Cone IsLimit)
open CategoryTheory.Limits.Types (sectionOfCone)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

/-- Cone compatibility on points: the image of a limiting point in stage `j` is
the image of its stage-`i` image under the transition morphism. -/
theorem points_map_w {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt)
    {i j : OrderDual I} (f : i ⟶ j) :
    Points.map (D.map f) (Points.map (c.π.app i) x) =
      Points.map (c.π.app j) x :=
  sorry

/-- The reduced point-closure morphism attached to a transition in the inverse
system. -/
def pointClosureMap {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt)
    {i j : OrderDual I} (f : i ⟶ j) :
    PointClosure.space (Points.map (c.π.app i) x) ⟶
      PointClosure.space (Points.map (c.π.app j) x) :=
  PointClosure.mapOfEq (D.map f) (Points.map (c.π.app i) x)
    (Points.map (c.π.app j) x) (points_map_w D c x f)

/-- The reduced point-closure map of an identity transition is the identity. -/
theorem pointClosureMap_id {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt)
    (i : OrderDual I) :
    pointClosureMap D c x (𝟙 i) =
      𝟙 (PointClosure.space (Points.map (c.π.app i) x)) :=
  sorry

/-- Reduced point-closure maps attached to transitions preserve composition. -/
theorem pointClosureMap_comp {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt)
    {i j k : OrderDual I} (f : i ⟶ j) (g : j ⟶ k) :
    pointClosureMap D c x (f ≫ g) =
      pointClosureMap D c x f ≫ pointClosureMap D c x g :=
  sorry

/-- The inverse diagram of reduced closures of the stagewise images of a
point. -/
def pointClosureDiagram {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt) :
    OrderDual I ⥤ AlgebraicSpace S where
  obj i := PointClosure.space (Points.map (c.π.app i) x)
  map f := pointClosureMap D c x f
  map_id := pointClosureMap_id D c x
  map_comp := pointClosureMap_comp D c x

/-- The object mapping of `pointClosureDiagram` is the reduced closure of the
stagewise image of the point. -/
theorem pointClosureDiagram_obj {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt)
    (i : OrderDual I) :
    (pointClosureDiagram D c x).obj i =
      PointClosure.space (Points.map (c.π.app i) x) :=
  sorry

/-- The canonical map from the reduced closure of a limiting point to a
stagewise closure. -/
def pointClosureToStage {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt)
    (i : OrderDual I) :
    PointClosure.space x ⟶ (pointClosureDiagram D c x).obj i :=
  PointClosure.mapOfEq (c.π.app i) x (Points.map (c.π.app i) x) rfl

/-- The maps from the reduced closure of the limiting point are natural in the
stage. -/
theorem pointClosureToStage_naturality {I : Type u} [Preorder I]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D)
    (x : Points c.pt) {i j : OrderDual I} (f : i ⟶ j) :
    pointClosureToStage D c x i ≫ (pointClosureDiagram D c x).map f =
      pointClosureToStage D c x j :=
  sorry

/-- The canonical cone of reduced point closures over the inverse system of
stagewise closures, with apex the reduced closure of the limiting point. -/
def pointClosureCone {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt) :
    Cone (pointClosureDiagram D c x) where
  pt := PointClosure.space x
  π :=
    { app := pointClosureToStage D c x
      naturality := fun _ j f ↦
        (Category.id_comp (pointClosureToStage D c x j)).trans
          (pointClosureToStage_naturality D c x f).symm }

/-- The apex of `pointClosureCone` is the reduced closure of the limiting
point. -/
theorem pointClosureCone_pt {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (x : Points c.pt) :
    (pointClosureCone D c x).pt = PointClosure.space x :=
  sorry

/-- For a limiting cone of a directed inverse system of decent algebraic spaces
over `S` with affine transition morphisms, a point of the limit lies in the
closure of `x` if and only if each of its stagewise images lies in the
corresponding stagewise closure. -/
theorem mem_closure_iff {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (x y : Points c.pt) :
    y ∈ (PointClosure.closedSubset x : Set (Points c.pt)) ↔
      ∀ i : OrderDual I,
        Points.map (c.π.app i) y ∈
          (PointClosure.closedSubset (Points.map (c.π.app i) x) :
            Set (Points (D.obj i))) :=
  sorry

/-- The reduced induced algebraic space on the closure of a point of a
directed affine inverse limit of decent algebraic spaces is a limit of the
stagewise reduced point-closure spaces. -/
theorem nonempty_isLimit_pointClosureCone {I : Type u} [Preorder I]
    [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (x : Points c.pt) :
    Nonempty (IsLimit (pointClosureCone D c x)) :=
  sorry

/-- The canonical comparison on points of the reduced point-closure cone is
bijective. -/
theorem bijective_sectionOfCone_pointClosureSet {I : Type u} [Preorder I]
    [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    [∀ i : OrderDual I, IsDecent (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (x : Points c.pt) :
    Function.Bijective
      (sectionOfCone (pointsFunctor.mapCone (pointClosureCone D c x))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
