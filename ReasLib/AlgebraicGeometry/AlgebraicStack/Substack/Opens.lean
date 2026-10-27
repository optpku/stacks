/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Substack.Open

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The restricted groupoid fibration of an open substack. -/
def category (U : Substack.Open X) : GroupoidsOver S :=
  Substack.category X U.val U.property.2.choose

/-- The literal inclusion of an open substack into its ambient stack. -/
def inclusion (U : Substack.Open X) : category U ⟶ X :=
  Substack.inclusion X U.val U.property.2.choose

/-- The restricted groupoid fibration of an open substack is an algebraic stack. -/
instance instAlgebraicStack_category (U : Substack.Open X) :
    AlgebraicStack (category U) :=
  U.property.2.choose_spec.1

/-- The literal inclusion of an open substack is an open immersion. -/
instance instOpenImmersion_inclusion (U : Substack.Open X) :
    Groupoids.Hom.OpenImmersion (inclusion U) :=
  U.property.2.choose_spec.2

variable [AlgebraicStack X]

/-- The image of the points of an open substack under its literal inclusion. -/
def pointsSet (U : Substack.Open X) : Set (Points X) :=
  Set.range (Points.map (inclusion U))

/-- The point image of an open substack is open in the canonical point topology. -/
theorem isOpen_pointsSet (U : Substack.Open X) :
    _root_.IsOpen (pointsSet U) := sorry

/-- The open subset of the point space determined by an open substack. -/
def pointsOpens (U : Substack.Open X) : TopologicalSpace.Opens (Points X) :=
  ⟨pointsSet U, isOpen_pointsSet U⟩

/-- Taking the point image bijects open substacks with open subsets of the point space. -/
theorem pointsOpens_bijective :
    Function.Bijective (pointsOpens (X := X)) := sorry

/-- Inclusion of point images is equivalent to inclusion of open substacks. -/
theorem pointsSet_subset_iff (U V : Substack.Open X) :
    pointsSet U ⊆ pointsSet V ↔ U.val ≤ V.val := sorry

/-- The objects whose Yoneda representatives have point image contained in an open set. -/
def ofOpensObjects (W : TopologicalSpace.Opens (Points X)) : ObjectProperty X.total :=
  fun y ↦ Set.range (Points.map
    (FiberedCategoryOver.Groupoids.YonedaSlice.representative
      (⟨y, rfl⟩ : X.p.Fiber (X.p.obj y)))) ⊆ W

/-- Objects whose Yoneda point images lie in an open set form an open substack. -/
theorem ofOpensObjects_isOpen (W : TopologicalSpace.Opens (Points X)) :
    Substack.IsOpen X (ofOpensObjects W) := sorry

/-- The open substack defined by requiring Yoneda point images to lie in a given open set. -/
def ofOpens (W : TopologicalSpace.Opens (Points X)) : Substack.Open X :=
  ⟨ofOpensObjects W, ofOpensObjects_isOpen W⟩

/-- The point image of the open substack defined by an open set is that set. -/
theorem ofOpens_pointsSet (W : TopologicalSpace.Opens (Points X)) :
    pointsSet (ofOpens W) = W := sorry

end AlgebraicGeometry.AlgebraicStack.Substack.Open
