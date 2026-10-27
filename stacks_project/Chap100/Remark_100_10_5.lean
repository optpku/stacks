/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicStack TopologicalSpace CategoryTheory
open AlgebraicGeometry.Groupoids.Hom

universe u

/- Remark 100.10.5: a locally closed subset `T ⊂ Points X` of an algebraic stack
`X` over a scheme `S` has a reduced induced substack structure, obtained as the
reduced closed substack of the open substack `U` with
`Substack.Open.pointsSet U = (∂T)ᶜ`, where `∂T = closure T \ T`. -/
@[stacks 06FK] #check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.stack :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    LocallyCloseds (Points X) → GroupoidsOver S)

section

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
  (T : LocallyCloseds (Points X))

#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.boundary T : Set (Points X))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.boundary_eq T :
  LocallyClosedReduction.boundary T = closure (T : Set (Points X)) \ (T : Set (Points X)))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.coborder_eq_compl_boundary T :
  coborder (T : Set (Points X)) = (LocallyClosedReduction.boundary T)ᶜ)
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.ambientOpen T : Substack.Open X)
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.ambientOpen_pointsSet T :
  Substack.Open.pointsSet (LocallyClosedReduction.ambientOpen T) = coborder (T : Set (Points X)))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.closedSubset T :
  Closeds (Points (Substack.Open.category (LocallyClosedReduction.ambientOpen T))))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.isClosed_preimage T :
  IsClosed (Points.map (Substack.Open.inclusion (LocallyClosedReduction.ambientOpen T)) ⁻¹'
    (T : Set (Points X))))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.coe_closedSubset T :
  (LocallyClosedReduction.closedSubset T :
    Set (Points (Substack.Open.category (LocallyClosedReduction.ambientOpen T)))) =
      Points.map (Substack.Open.inclusion (LocallyClosedReduction.ambientOpen T)) ⁻¹'
        (T : Set (Points X)))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.closedStructure T :
  ClosedSubstackStructure (LocallyClosedReduction.closedSubset T))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.ιToAmbientOpen T :
  LocallyClosedReduction.stack T ⟶ Substack.Open.category (LocallyClosedReduction.ambientOpen T))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.ι T :
  LocallyClosedReduction.stack T ⟶ X)
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.instOpenImmersion_ambientOpen_ι T :
  OpenImmersion (Substack.Open.inclusion (LocallyClosedReduction.ambientOpen T)))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.instClosedImmersion_ιToAmbientOpen T :
  ClosedImmersion (LocallyClosedReduction.ιToAmbientOpen T))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.instImmersion_ι T :
  Immersion (LocallyClosedReduction.ι T))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.instIsReduced_stack T :
  IsReduced (LocallyClosedReduction.stack T))
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.range_ιToAmbientOpen T :
  Set.range (Points.map (LocallyClosedReduction.ιToAmbientOpen T)) =
    LocallyClosedReduction.closedSubset T)
#check (AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction.range_ι T :
  Set.range (Points.map (LocallyClosedReduction.ι T)) = T)

end
