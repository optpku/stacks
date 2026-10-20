module

public import Mathlib.Topology.Defs.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-!
# Coborder factorization of immersions of algebraic spaces

An immersion `f : Z ⟶ X` of algebraic spaces has locally closed image in
`Points X`. Its coborder is therefore open, and `f` lifts uniquely through the
corresponding open subspace as a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsImmersion

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}

/-- The boundary of the image of `|Z|` in `|X|` along a morphism of algebraic
spaces. -/
def imageBoundary (f : Z ⟶ X) : Set (Points X) :=
  closure (Set.range (Points.map f)) \ Set.range (Points.map f)

/-- `imageBoundary f` is the complement of the image of `Points.map f` in its
closure. -/
theorem imageBoundary_eq (f : Z ⟶ X) :
    imageBoundary f =
      closure (Set.range (Points.map f)) \ Set.range (Points.map f) :=
  sorry

/-- The image boundary is the complement of the coborder of the image of
points. -/
theorem imageBoundary_eq_compl_coborder (f : Z ⟶ X) :
    imageBoundary f = (coborder (Set.range (Points.map f)))ᶜ :=
  sorry

variable (f : Z ⟶ X) [IsImmersion f]

/-- The image of an immersion is locally closed, so its boundary in `|X|` is
closed. -/
instance imageBoundary_isClosed : IsClosed (imageBoundary f) := sorry

/-- The image boundary of an immersion, as a closed subset of `|X|`. -/
def imageBoundaryCloseds : Closeds (Points X) :=
  ⟨imageBoundary f, imageBoundary_isClosed f⟩

/-- The carrier of `imageBoundaryCloseds f` is `imageBoundary f`. -/
theorem imageBoundaryCloseds_carrier :
    (imageBoundaryCloseds f).carrier = imageBoundary f :=
  sorry

/-- The reduced induced closed subspace `∂Z` of `X` supported on the image
boundary of `f`. -/
def imageBoundarySubspace : ClosedSubspaceStructure (imageBoundaryCloseds f) :=
  ClosedSubspaceStructure.reduced (imageBoundaryCloseds f)

/-- `imageBoundarySubspace f` is the reduced induced closed subspace of `X` with
point-set `imageBoundary f`. -/
theorem imageBoundarySubspace_spec :
    (imageBoundarySubspace f).subspace.pointsSet = imageBoundary f ∧
      hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
        (imageBoundarySubspace f).space ∧
      IsClosedImmersion (imageBoundarySubspace f).ι :=
  sorry

/-- The inclusion of the reduced image-boundary subspace is a closed
immersion. -/
instance isClosedImmersion_imageBoundarySubspace_ι :
    IsClosedImmersion (imageBoundarySubspace f).ι :=
  (imageBoundarySubspace f).subspace.isClosedImmersion

/-- The coborder of the image of an immersion is open in `|X|`. -/
theorem isOpen_coborder_range :
    IsOpen (coborder (Set.range (Points.map f))) :=
  sorry

/-- The open subspace `X \ ∂Z` of `X` whose points are the coborder of the
image of `f`. -/
def coborderRange : OpenSubspace X :=
  OpenSubspace.fromOpens
    ⟨coborder (Set.range (Points.map f)), isOpen_coborder_range f⟩

/-- The point-set of `coborderRange f` is the coborder of the image of
`Points.map f`. -/
theorem coborderRange_pointsSet :
    (coborderRange f).pointsSet = coborder (Set.range (Points.map f)) :=
  sorry

/-- The coborder range is an open subspace complementary to the reduced image
boundary. -/
theorem coborderRange_spec :
    IsOpenImmersion (coborderRange f).ι ∧
      (coborderRange f).pointsSet =
        (imageBoundarySubspace f).subspace.pointsSetᶜ :=
  sorry

/-- The inclusion of the coborder range of an immersion is an open immersion. -/
instance isOpenImmersion_coborderRange_ι :
    IsOpenImmersion (coborderRange f).ι :=
  (coborderRange f).isOpenImmersion

/-- The image of an immersion lands in its coborder range. -/
theorem range_subset_coborderRange :
    Set.range (Points.map f) ⊆ (coborderRange f).pointsSet :=
  sorry

/-- An immersion factors uniquely through its coborder open subspace. -/
theorem exists_liftCoborder :
    ∃ g : Z ⟶ (coborderRange f).X, g ≫ (coborderRange f).ι = f :=
  sorry

/-- The closed-immersion stage of the coborder factorization of `f`. -/
def liftCoborder : Z ⟶ (coborderRange f).X :=
  OpenSubspace.Construction.lift f (by
    change Set.range (Points.map f) ⊆ coborder (Set.range (Points.map f))
    sorry)

/-- The coborder lift composed with the coborder inclusion recovers `f`. -/
theorem liftCoborder_comp : liftCoborder f ≫ (coborderRange f).ι = f :=
  sorry

/-- The coborder lift of an immersion is a closed immersion. -/
instance isClosedImmersion_liftCoborder : IsClosedImmersion (liftCoborder f) :=
  sorry

/-- The image of the coborder lift is closed in the coborder range. -/
instance isClosed_range_points_liftCoborder :
    IsClosed (Set.range (Points.map (liftCoborder f))) :=
  sorry

end IsImmersion

end AlgebraicGeometry.AlgebraicSpace
