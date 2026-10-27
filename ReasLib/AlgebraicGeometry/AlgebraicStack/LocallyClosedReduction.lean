/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion.Composition
public import ReasLib.Topology.LocallyClosed.Subsets

/-!
# Reduced induced algebraic stacks on locally closed subsets

A locally closed subset of the point space determines an open substack on its
coborder, followed by the reduced induced closed substack on its inverse image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The boundary of a locally closed subset is its closure minus the subset itself. -/
def boundary (T : LocallyCloseds (Points X)) : Set (Points X) :=
  closure (T : Set (Points X)) \ (T : Set (Points X))

/-- The boundary is the complement of a locally closed subset in its closure. -/
theorem boundary_eq (T : LocallyCloseds (Points X)) :
    boundary T = closure (T : Set (Points X)) \ (T : Set (Points X)) := sorry

/-- The coborder of a locally closed subset is the complement of its boundary. -/
theorem coborder_eq_compl_boundary (T : LocallyCloseds (Points X)) :
    coborder (T : Set (Points X)) = (boundary T)ᶜ := sorry

/-- The open substack occupying the complement of the boundary of a locally closed subset. -/
def ambientOpen (T : LocallyCloseds (Points X)) : Substack.Open X :=
  Substack.Open.ofOpens ⟨coborder (T : Set (Points X)), T.property.isOpen_coborder⟩

/-- The inclusion of the ambient open of a locally closed subset is an open immersion. -/
instance instOpenImmersion_ambientOpen_ι (T : LocallyCloseds (Points X)) :
    OpenImmersion (Substack.Open.inclusion (ambientOpen T)) :=
  Substack.Open.instOpenImmersion_inclusion (ambientOpen T)

/-- The point image of the ambient open is the coborder of the locally closed subset. -/
theorem ambientOpen_pointsSet (T : LocallyCloseds (Points X)) :
    Substack.Open.pointsSet (ambientOpen T) = coborder (T : Set (Points X)) := sorry

/-- A locally closed subset pulls back to a closed subset of its ambient open. -/
theorem isClosed_preimage (T : LocallyCloseds (Points X)) :
    _root_.IsClosed (Points.map (Substack.Open.inclusion (ambientOpen T)) ⁻¹'
      (T : Set (Points X))) := sorry

/-- The closed subset of the ambient open obtained by pulling back the locally closed subset. -/
def closedSubset (T : LocallyCloseds (Points X)) :
    Closeds (Points (Substack.Open.category (ambientOpen T))) where
  carrier := Points.map (Substack.Open.inclusion (ambientOpen T)) ⁻¹' (T : Set (Points X))
  isClosed' := isClosed_preimage T

/-- The carrier of the closed subset is the inverse image under the ambient inclusion on points. -/
theorem coe_closedSubset (T : LocallyCloseds (Points X)) :
    (closedSubset T : Set (Points (Substack.Open.category (ambientOpen T)))) =
      Points.map (Substack.Open.inclusion (ambientOpen T)) ⁻¹' (T : Set (Points X)) := sorry

/-- The reduced induced closed structure inside the ambient open of a locally closed subset. -/
abbrev closedStructure (T : LocallyCloseds (Points X)) :
    ClosedSubstackStructure (closedSubset T) :=
  ClosedSubstackStructure.reduced (closedSubset T)

/-- The reduced induced algebraic stack on a locally closed subset of the point space. -/
abbrev stack (T : LocallyCloseds (Points X)) : GroupoidsOver S :=
  (closedStructure T).Y

/-- The reduced induced stack on a locally closed subset is reduced. -/
instance instIsReduced_stack (T : LocallyCloseds (Points X)) : IsReduced (stack T) :=
  (ClosedSubstackStructure.reduced_spec (closedSubset T)).2

/-- The canonical closed inclusion of the reduced induced stack into its ambient open. -/
abbrev ιToAmbientOpen (T : LocallyCloseds (Points X)) :
    stack T ⟶ Substack.Open.category (ambientOpen T) :=
  (closedStructure T).ι

/-- The canonical inclusion into the ambient open is a closed immersion. -/
instance instClosedImmersion_ιToAmbientOpen (T : LocallyCloseds (Points X)) :
    ClosedImmersion (ιToAmbientOpen T) :=
  (ClosedSubstackStructure.spec (closedStructure T)).1

/-- The closed-stage inclusion has point image equal to the prescribed closed subset. -/
theorem range_ιToAmbientOpen (T : LocallyCloseds (Points X)) :
    Set.range (Points.map (ιToAmbientOpen T)) = closedSubset T := sorry

/-- The canonical immersion is the closed-stage inclusion followed by the ambient open inclusion. -/
abbrev ι (T : LocallyCloseds (Points X)) : stack T ⟶ X :=
  ιToAmbientOpen T ≫ Substack.Open.inclusion (ambientOpen T)

/-- The canonical inclusion of a reduced induced locally closed stack is an immersion. -/
instance instImmersion_ι (T : LocallyCloseds (Points X)) : Immersion (ι T) :=
  Immersion.comp (ιToAmbientOpen T) (Substack.Open.inclusion (ambientOpen T))

/-- The canonical immersion has point image exactly the original locally closed subset. -/
theorem range_ι (T : LocallyCloseds (Points X)) :
    Set.range (Points.map (ι T)) = T := sorry

end AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction
