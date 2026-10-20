/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition
public import ReasLib.Topology.LocallyClosed.Subsets

/-!
# Reduced induced algebraic spaces on locally closed subsets

A locally closed subset `T` of `Points X` determines an open subspace `U` with
point-set `coborder T`, and then the reduced induced closed subspace of `U` on
`T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.LocallyClosedReduction

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The boundary of a locally closed subset of `Points X`, as `closure T \ T`. -/
def boundary (T : LocallyCloseds (Points X)) : Set (Points X) :=
  closure (T : Set (Points X)) \ (T : Set (Points X))

/-- The boundary is the complement of `T` in its closure. -/
theorem boundary_eq (T : LocallyCloseds (Points X)) :
    boundary T = closure (T : Set (Points X)) \ (T : Set (Points X)) :=
  rfl

/-- The coborder of `T` is the complement of the boundary. -/
theorem coborder_eq_compl_boundary (T : LocallyCloseds (Points X)) :
    coborder (T : Set (Points X)) = (boundary T)ᶜ :=
  rfl

/-- The open subspace of `X` with underlying point-set `Points X \ boundary T`. -/
def ambientOpen (T : LocallyCloseds (Points X)) : OpenSubspace X :=
  OpenSubspace.fromOpens ⟨coborder (T : Set (Points X)), T.property.isOpen_coborder⟩

/-- The inclusion of the ambient open is an open immersion. -/
def isOpenImmersion_ambientOpen_ι (T : LocallyCloseds (Points X)) :
    IsOpenImmersion (ambientOpen T).ι :=
  (ambientOpen T).isOpenImmersion

/-- The underlying point-set of the ambient open is the coborder of `T`. -/
theorem ambientOpen_pointsSet (T : LocallyCloseds (Points X)) :
    (ambientOpen T).pointsSet = coborder (T : Set (Points X)) :=
  OpenSubspace.fromOpens_pointsSet
    ⟨coborder (T : Set (Points X)), T.property.isOpen_coborder⟩

/-- The locally closed subset `T`, viewed as a closed subset of the ambient open. -/
def closedSubset (T : LocallyCloseds (Points X)) :
    Closeds (Points (ambientOpen T).X) where
  carrier := Points.map (ambientOpen T).ι ⁻¹' (T : Set (Points X))
  isClosed' := sorry

/-- The closed subset is the inverse image of `T` under the ambient open inclusion
on points. -/
theorem coe_closedSubset (T : LocallyCloseds (Points X)) :
    (closedSubset T : Set (Points (ambientOpen T).X)) =
      Points.map (ambientOpen T).ι ⁻¹' (T : Set (Points X)) :=
  rfl

/-- The reduced induced closed-subspace structure on `T` inside the ambient open. -/
abbrev closedStructure (T : LocallyCloseds (Points X)) :
    ClosedSubspaceStructure (closedSubset T) :=
  ClosedSubspaceStructure.reduced (closedSubset T)

/-- The reduced induced algebraic space on a locally closed subset. -/
abbrev space (T : LocallyCloseds (Points X)) : AlgebraicSpace S :=
  (closedStructure T).space

/-- The closed immersion into the ambient open subspace. -/
abbrev ιToAmbientOpen (T : LocallyCloseds (Points X)) :
    space T ⟶ (ambientOpen T).X :=
  (closedStructure T).ι

/-- The closed stage is a closed immersion. -/
def isClosedImmersion_ιToAmbientOpen (T : LocallyCloseds (Points X)) :
    IsClosedImmersion (ιToAmbientOpen T) :=
  (closedStructure T).subspace.isClosedImmersion

/-- The closed stage has image equal to the prescribed closed subset of the ambient
open. -/
theorem range_ιToAmbientOpen (T : LocallyCloseds (Points X)) :
    Set.range (Points.map (ιToAmbientOpen T)) = closedSubset T :=
  (closedStructure T).pointsSet_eq

/-- The canonical immersion of the reduced induced space into `X`. -/
abbrev ι (T : LocallyCloseds (Points X)) : space T ⟶ X :=
  ιToAmbientOpen T ≫ (ambientOpen T).ι

/-- The canonical map of a locally closed induced space is an immersion. -/
def isImmersion_ι (T : LocallyCloseds (Points X)) :
    IsImmersion (ι T) :=
  @IsImmersion.comp S _ _ _ (ιToAmbientOpen T) (ambientOpen T).ι
    (@IsImmersion.ofIsClosedImmersion S _ _ _ (isClosedImmersion_ιToAmbientOpen T))
    (@IsImmersion.ofIsOpenImmersion S _ _ _ (isOpenImmersion_ambientOpen_ι T))

/-- The reduced induced space is reduced in the étale-local sense. -/
theorem isReduced_space (T : LocallyCloseds (Points X)) :
    hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) (space T) :=
  (ClosedSubspaceStructure.reduced_spec (closedSubset T)).2

/-- The canonical immersion has set-theoretic range exactly `T`. -/
theorem range_ι (T : LocallyCloseds (Points X)) :
    Set.range (Points.map (ι T)) = T :=
  sorry

/-- The reduced induced space on `T` is obtained by a closed immersion into the
open complement of the boundary, hence an immersion into `X`, and is reduced with
point-set `T`. -/
theorem spec (T : LocallyCloseds (Points X)) :
    (ambientOpen T).pointsSet = (boundary T)ᶜ ∧
      IsOpenImmersion (ambientOpen T).ι ∧
      IsClosedImmersion (ιToAmbientOpen T) ∧
      IsImmersion (ι T) ∧
      hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) (space T) ∧
      Set.range (Points.map (ι T)) = (T : Set (Points X)) :=
  ⟨(ambientOpen_pointsSet T).trans (coborder_eq_compl_boundary T),
    isOpenImmersion_ambientOpen_ι T, isClosedImmersion_ιToAmbientOpen T,
    isImmersion_ι T, isReduced_space T, range_ι T⟩

/-- The reduced induced space on `T`, as a locally closed subspace of `X`. -/
def toLocallyClosedSubspace (T : LocallyCloseds (Points X)) :
    LocallyClosedSubspace X where
  X := space T
  ι := ι T
  isImmersion := isImmersion_ι T

/-- The inclusion of `toLocallyClosedSubspace T` is the canonical immersion. -/
theorem toLocallyClosedSubspace_ι (T : LocallyCloseds (Points X)) :
    (toLocallyClosedSubspace T).ι = ι T :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.LocallyClosedReduction

namespace AlgebraicGeometry.AlgebraicSpace.LocallyClosedSubspace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The reduced induced subspace structure on a locally closed subset of `Points X`. -/
def reduced (T : LocallyCloseds (Points X)) : LocallyClosedSubspace X :=
  LocallyClosedReduction.toLocallyClosedSubspace T

/-- The inclusion of the reduced induced subspace structure is the canonical immersion. -/
theorem reduced_ι (T : LocallyCloseds (Points X)) :
    (reduced T).ι = LocallyClosedReduction.ι T :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.LocallyClosedSubspace
