/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Comparison
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.ToInertia
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.StrongTrans

/-!
# Relative inertia as a pseudo-comma action

Aggregate import for relative inertia on the pseudo-comma bicategory of
arrows over a fixed base. `Action.Construction` owns the square and `2`-cell
data, `Action.Computations` owns their readouts, and `Comparison` owns the
identity and composition comparison cells.
`ToInertia` specializes the relative-to-absolute comparison to pseudo-comma
squares and its `2`-cell naturality.
The preferred lower-level readout is
`BasedCategory.RelativeInertia.pseudoComma.{map,map₂,mapFunctor,mapIso}`.
The relative-to-absolute comparison is owned by `pseudoComma.toInertiaIso`, while
`Pseudofunctor.Construction` owns the coherence package and `Pseudofunctor.Computations` exposes
only the bridges
`pseudoComma.pseudofunctor.{obj,map,map₂,mapFunctor,mapId,mapComp}`. Equivalences are mapped by
the generic `Pseudofunctor.mapEquivalence` API rather than a relative-inertia wrapper.
The stable-universe transformations
`pseudoComma.{forget,identitySection}.strongTrans` are owned by the focused `StrongTrans` leaves.

Import a leaf module when only one layer is required. This path remains the
stable complete entry point for the action and is used by the pseudofunctor
packaging.
-/

@[expose] public section
