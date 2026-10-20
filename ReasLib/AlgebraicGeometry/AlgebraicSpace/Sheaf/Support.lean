module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AdditiveAdjunction

/-!
# Geometric stalks and support of abelian sheaves

Geometric stalks are inverse images along geometric points followed by sections over their
source spectra. The support consists of points with a nonzero geometric stalk.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Sections over `Spec(p.K)`, sending a sheaf of abelian groups on the small étale site of the
source to its value on the identity object. -/
def abelianSectionsFunctor (p : FieldValuedPoint X) :
    Sheaf (smallEtaleTopology (ofOver p.overObj)) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (smallEtaleTopology (ofOver p.overObj)) AddCommGrpCat.{u} ⋙
    (evaluation (smallEtaleSite (ofOver p.overObj))ᵒᵖ AddCommGrpCat.{u}).obj (op p.sourceObj)

/-- Sections of a sheaf of abelian groups over the identity object of `Spec(p.K)`. -/
theorem abelianSectionsFunctor_obj (p : FieldValuedPoint X)
    (G : Sheaf (smallEtaleTopology (ofOver p.overObj)) AddCommGrpCat.{u}) :
    (abelianSectionsFunctor p).obj G = G.obj.obj (op p.sourceObj) := by
  rfl

/-- The geometric stalk of a sheaf of abelian groups at a geometric point, as inverse image along
the point morphism followed by sections over `Spec(k)`. -/
def abelianGeometricStalk (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})
    (xbar : GeometricPoint X) : AddCommGrpCat.{u} :=
  (abelianSectionsFunctor xbar.toFieldValuedPoint).obj
    ((EtaleAdditive.inverseImage xbar.hom).obj F)

/-- The geometric stalk of a sheaf of abelian groups is inverse image along `xbar.hom`, then
sections over `Spec(k)`. -/
theorem abelianGeometricStalk_eq (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})
    (xbar : GeometricPoint X) :
    abelianGeometricStalk F xbar =
      (abelianSectionsFunctor xbar.toFieldValuedPoint).obj
        ((EtaleAdditive.inverseImage xbar.hom).obj F) := by
  rfl

/-- Whether the geometric stalk of a sheaf of abelian groups is zero depends only on the image
point in `|X|`. -/
theorem abelianGeometricStalk_isZero_iff_of_image_eq
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) (xbar tbar : GeometricPoint X)
    (himage : xbar.image = tbar.image) :
    IsZero (abelianGeometricStalk F xbar) ↔ IsZero (abelianGeometricStalk F tbar) :=
  sorry

/-- The underlying type-valued presheaf of an abelian sheaf on `X_étale`. -/
def abelianTypePresheaf (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{v}) :
    (smallEtaleSite X)ᵒᵖ ⥤ Type v :=
  F.obj ⋙ forget AddCommGrpCat.{v}

/-- The type-valued presheaf of an abelian sheaf is the forgetful image of its underlying
presheaf. -/
theorem abelianTypePresheaf_eq (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{v}) :
    abelianTypePresheaf F = F.obj ⋙ forget AddCommGrpCat.{v} := sorry

/-- The support of an abelian sheaf on the small étale site, as the points of `|X|` admitting a
geometric point with nonzero geometric stalk. -/
def abelianSheafSupport (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{v}) :
    Set (Points X) :=
  {x | ∃ xbar : GeometricPoint X,
    xbar.image = x ∧ ¬ Subsingleton (GeometricPoint.stalk xbar (abelianTypePresheaf F))}

/-- Membership in the étale abelian-sheaf support is existence of a geometric point over the
point with nonzero geometric stalk. -/
theorem mem_abelianSheafSupport_iff_typeStalk (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{v})
    (x : Points X) :
    x ∈ abelianSheafSupport F ↔
      ∃ xbar : GeometricPoint X,
        xbar.image = x ∧ ¬ Subsingleton (GeometricPoint.stalk xbar (abelianTypePresheaf F)) := by
  rfl

/-- Geometric stalks of an abelian sheaf have the same subsingleton property for geometric
points with the same image in `|X|`. -/
theorem abelianSheafSupport_subsingleton_iff_of_image_eq
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{v})
    (xbar tbar : GeometricPoint X) (himage : xbar.image = tbar.image) :
    Subsingleton (GeometricPoint.stalk xbar (abelianTypePresheaf F)) ↔
      Subsingleton (GeometricPoint.stalk tbar (abelianTypePresheaf F)) := sorry

/-- For any geometric point, support membership of its image is equivalent to nonvanishing of
its geometric stalk; this is independent of the chosen geometric point over the same point of
`|X|`. -/
theorem mem_abelianSheafSupport_iff_stalk
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{v}) (xbar : GeometricPoint X) :
    xbar.image ∈ abelianSheafSupport F ↔
      ¬ Subsingleton (GeometricPoint.stalk xbar (abelianTypePresheaf F)) := sorry

/-- The underlying geometric stalk of an abelian sheaf is subsingleton exactly when its
additive geometric stalk is a zero object. -/
theorem abelianTypeStalk_subsingleton_iff_isZero
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) (xbar : GeometricPoint X) :
    Subsingleton (GeometricPoint.stalk xbar (abelianTypePresheaf F)) ↔
      IsZero (abelianGeometricStalk F xbar) := sorry

/-- Membership in the support of an abelian sheaf is existence of a geometric point over the
point whose additive geometric stalk is nonzero. -/
theorem mem_abelianSheafSupport_iff
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) (x : Points X) :
    x ∈ abelianSheafSupport F ↔
      ∃ xbar : GeometricPoint X, xbar.image = x ∧ ¬ IsZero (abelianGeometricStalk F xbar) := by
  simp only [mem_abelianSheafSupport_iff_typeStalk, abelianTypeStalk_subsingleton_iff_isZero]

end AlgebraicGeometry.AlgebraicSpace
