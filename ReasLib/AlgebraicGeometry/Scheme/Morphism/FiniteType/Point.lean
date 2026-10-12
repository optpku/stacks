/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Extension
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite type points of a scheme

A point of a scheme is of finite type when its canonical residue-field point is a finite-type
morphism. This module also characterizes finite-type field-valued points through affine coordinate
rings and residue-field extensions.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory

/-- A point is of finite type when its canonical residue-field morphism is of finite type. -/
@[stacks 02J1 "finite type point"]
abbrev IsFiniteTypePoint {S : Scheme.{u}} (s : S) : Prop :=
  Scheme.Hom.FiniteType (S.fromSpecResidueField s)

/-- Unfold the finite type point predicate into the canonical residue-field morphism condition. -/
theorem isFiniteTypePoint_iff {S : Scheme.{u}} (s : S) :
    IsFiniteTypePoint s ↔ Scheme.Hom.FiniteType (S.fromSpecResidueField s) :=
  Iff.rfl

/-- The set of finite type points of a scheme. -/
@[stacks 02J1 "set of finite type points"]
def finiteTypePoints (S : Scheme.{u}) : Set S :=
  { s | IsFiniteTypePoint s }

/-- Membership in `finiteTypePoints S` is the finite type point property. -/
theorem mem_finiteTypePoints_iff (S : Scheme.{u}) (s : S) :
    s ∈ finiteTypePoints S ↔ IsFiniteTypePoint s :=
  Iff.rfl

namespace Scheme.Hom.FieldValuedPoint

variable {S : Scheme.{u}} {k : Type u} [Field k]

/-- A field-valued point has a finite coordinate-ring map on an affine open when it factors
through that open and the induced map on global sections is finite. -/
def HasFiniteCoordinateRingMapOnAffineOpen
    (f : Spec (CommRingCat.of k) ⟶ S) : Prop :=
  ∃ U : S.affineOpens,
    ∃ g : Spec (CommRingCat.of k) ⟶ S.restrict (U : S.Opens).isOpenEmbedding,
      g ≫ S.ofRestrict (U : S.Opens).isOpenEmbedding = f ∧
        (CommRingCat.Hom.hom (appTop g)).Finite

/-- A field-valued point has a finite coordinate-ring map on an affine open exactly when it
admits the corresponding affine-open factorization with finite induced map. -/
theorem hasFiniteCoordinateRingMapOnAffineOpen_iff
    (f : Spec (CommRingCat.of k) ⟶ S) :
    HasFiniteCoordinateRingMapOnAffineOpen f ↔
      ∃ U : S.affineOpens,
        ∃ g : Spec (CommRingCat.of k) ⟶ S.restrict (U : S.Opens).isOpenEmbedding,
          g ≫ S.ofRestrict (U : S.Opens).isOpenEmbedding = f ∧
            (CommRingCat.Hom.hom (appTop g)).Finite :=
  Iff.rfl

/-- A field-valued point has closed image with finite residue extension on an affine open when it
factors through that open, its image there is closed, and the induced residue-field extension is
finite. -/
def HasClosedImageWithFiniteResidueExtensionOnAffineOpen
    (f : Spec (CommRingCat.of k) ⟶ S) : Prop :=
  ∃ U : S.affineOpens,
    ∃ g : Spec (CommRingCat.of k) ⟶ S.restrict (U : S.Opens).isOpenEmbedding,
      g ≫ S.ofRestrict (U : S.Opens).isOpenEmbedding = f ∧
        closedPointImage g ∈ closedPoints (S.restrict (U : S.Opens).isOpenEmbedding) ∧
          HasFiniteResidueFieldExtension g

/-- A field-valued point has closed image with finite residue extension on an affine open exactly
when it admits the corresponding affine-open factorization. -/
theorem hasClosedImageWithFiniteResidueExtensionOnAffineOpen_iff
    (f : Spec (CommRingCat.of k) ⟶ S) :
    HasClosedImageWithFiniteResidueExtensionOnAffineOpen f ↔
      ∃ U : S.affineOpens,
        ∃ g : Spec (CommRingCat.of k) ⟶ S.restrict (U : S.Opens).isOpenEmbedding,
          g ≫ S.ofRestrict (U : S.Opens).isOpenEmbedding = f ∧
            closedPointImage g ∈ closedPoints (S.restrict (U : S.Opens).isOpenEmbedding) ∧
              HasFiniteResidueFieldExtension g :=
  Iff.rfl

/-- A field-valued point is of finite type if and only if it is locally of finite type. -/
theorem finiteType_iff_locallyOfFiniteType
    (f : Spec (CommRingCat.of k) ⟶ S) :
    FiniteType f ↔ LocallyOfFiniteType f := sorry

/-- A field-valued point is locally of finite type if and only if it has a finite coordinate-ring
map on an affine open. -/
theorem locallyOfFiniteType_iff_finiteCoordinateRingMapOnAffineOpen
    (f : Spec (CommRingCat.of k) ⟶ S) :
    LocallyOfFiniteType f ↔ HasFiniteCoordinateRingMapOnAffineOpen f := sorry

/-- A field-valued point has a finite coordinate-ring map on an affine open if and only if it has
closed image with finite residue extension on an affine open. -/
theorem finiteCoordinateRingMap_iff_closedImageFiniteResidueExtension
    (f : Spec (CommRingCat.of k) ⟶ S) :
    HasFiniteCoordinateRingMapOnAffineOpen f ↔
      HasClosedImageWithFiniteResidueExtensionOnAffineOpen f := sorry

/-- A field-valued point is locally of finite type if and only if it is of finite type at the
unique closed point of its source. -/
theorem locallyOfFiniteType_iff_finiteTypeAt_closedPoint
    (f : Spec (CommRingCat.of k) ⟶ S) :
    LocallyOfFiniteType f ↔ f.FiniteTypeAt (IsLocalRing.closedPoint k) := sorry

/-- A field-valued point has closed image with finite residue extension on an affine open if and
only if its image is a finite-type point and its residue-field extension is finite. -/
theorem closedImageFiniteResidueExtensionOnAffineOpen_iff_imageFiniteTypePoint
    (f : Spec (CommRingCat.of k) ⟶ S) :
    HasClosedImageWithFiniteResidueExtensionOnAffineOpen f ↔
      IsFiniteTypePoint (closedPointImage f) ∧ HasFiniteResidueFieldExtension f := sorry

/-- A field-valued point is of finite type if and only if its image is a finite-type point and its
residue-field extension is finite. -/
theorem finiteType_iff_imageFiniteTypePoint
    (f : Spec (CommRingCat.of k) ⟶ S) :
    FiniteType f ↔
      IsFiniteTypePoint (closedPointImage f) ∧ HasFiniteResidueFieldExtension f := sorry

/-- For a field-valued point, finite type, local finite type, finite affine coordinate-ring map,
and closed affine image with finite residue extension are equivalent. -/
theorem finiteType_tfae
    (f : Spec (CommRingCat.of k) ⟶ S) :
    List.TFAE [
      FiniteType f,
      LocallyOfFiniteType f,
      HasFiniteCoordinateRingMapOnAffineOpen f,
      HasClosedImageWithFiniteResidueExtensionOnAffineOpen f] := sorry

end Scheme.Hom.FieldValuedPoint

/-- The finite-type points of a scheme are the images of the closed points of its open
subschemes. -/
theorem finiteTypePoints_eq_iUnion_image_closedPoints_open (S : Scheme.{u}) :
    finiteTypePoints S =
      ⋃ U : S.Opens, (Subtype.val '' closedPoints U : Set S) := sorry

/-- The finite-type points of a scheme are the images of the closed points of its affine open
subschemes. -/
theorem finiteTypePoints_eq_iUnion_image_closedPoints_affineOpen (S : Scheme.{u}) :
    finiteTypePoints S =
      ⋃ U : S.affineOpens, (Subtype.val '' closedPoints U.1 : Set S) := sorry

namespace LocallyOfFiniteType

/-- A locally finite type morphism maps finite-type points to finite-type points. -/
theorem image_finiteTypePoints_subset
    {T S : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f] :
    f '' finiteTypePoints T ⊆ finiteTypePoints S := sorry

/-- A surjective locally finite type morphism maps the finite-type points of its source onto the
finite-type points of its target. -/
theorem image_finiteTypePoints_eq_of_surjective
    {T S : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f] [Surjective f] :
    f '' finiteTypePoints T = finiteTypePoints S := sorry

end LocallyOfFiniteType

end AlgebraicGeometry
