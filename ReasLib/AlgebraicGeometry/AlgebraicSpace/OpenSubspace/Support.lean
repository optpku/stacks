module

public import Mathlib.Topology.Sets.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-! # Points of open subspaces -/

@[expose] public section
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

/-- The underlying set of points of an open subspace, as the image of `|U| → |X|`. -/
def pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) : Set (Points X) :=
  Set.range (Points.map U.ι)

/-- `pointsSet U` is the range of `Points.map U.ι`. -/
theorem pointsSet_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    U.pointsSet = Set.range (Points.map U.ι) :=
  sorry

/-- A point of `|X|` lies in `pointsSet U` if and only if it is the image of a point of `|U|`. -/
theorem mem_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X)
    {x : Points X} :
    x ∈ U.pointsSet ↔ ∃ y : Points U.X, Points.map U.ι y = x :=
  sorry

/-- The identity open subspace occupies all of `|X|`. -/
theorem pointsSet_id {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (OpenSubspace.id X).pointsSet = Set.univ :=
  sorry

/-- The image `|U| ⊆ |X|` is open in the canonical topology on `|X|`. -/
theorem isOpen_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    IsOpen U.pointsSet :=
  sorry

/-- The image `|U| ⊆ |X|` as an open of the topological space `|X|`. -/
def pointsOpens {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    Opens (Points X) :=
  Opens.mk U.pointsSet (isOpen_pointsSet U)

/-- The carrier of `pointsOpens U` is `U.pointsSet`. -/
theorem pointsOpens_carrier {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    U.pointsOpens.carrier = U.pointsSet :=
  sorry

/-- Inclusion of underlying point-sets of open subspaces is equivalent to the existence of a
morphism over `X`. -/
theorem pointsSet_subset_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (U V : OpenSubspace X) :
    U.pointsSet ⊆ V.pointsSet ↔ ∃ f : U.X ⟶ V.X, f ≫ V.ι = U.ι :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
