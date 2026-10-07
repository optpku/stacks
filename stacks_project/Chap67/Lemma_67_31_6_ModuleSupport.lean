module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Remark_66_19_11_StalkFunctor

/-!
# Support of a sheaf of abelian groups and of an 𝒪_X-module

The geometric stalk of an abelian sheaf at a geometric point of an algebraic space is inverse
image along the point morphism, followed by sections over the source spectrum. The support is
the locus in `|X|` where this stalk is a nonzero abelian group. The support of an `𝒪_X`-module
is the support of its underlying abelian sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The opposite of étale base change admits left Kan extensions of abelian-group-valued
presheaves. -/
instance etaleBaseChange_op_hasLeftKanExtension_addCommGrp {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : (smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (etaleBaseChange f).op.HasLeftKanExtension F :=
  sorry

/-- Abelian-group-valued weak sheafification exists on the étale site of algebraic spaces. -/
instance spacesEtaleTopology_hasWeakSheafify_addCommGrp (X : AlgebraicSpace S) :
    HasWeakSheafify (spacesEtaleTopology X) AddCommGrpCat.{u} :=
  sorry

variable {X : AlgebraicSpace S}

/-- Sections over `Spec(p.K)`, sending a sheaf of abelian groups on the small étale site of the
source to its value on the identity object. -/
def abelianSectionsFunctor (p : FieldValuedPoint X) :
    Sheaf (smallEtaleTopology (ofOver p.overObj)) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (smallEtaleTopology (ofOver p.overObj)) AddCommGrpCat.{u} ⋙
    (evaluation (smallEtaleSite (ofOver p.overObj))ᵒᵖ AddCommGrpCat.{u}).obj (op p.sourceObj)

/-- Sections of a sheaf of abelian groups over the identity object of `Spec(p.K)`. -/
theorem abelianSectionsFunctor_obj (p : FieldValuedPoint X)
    (G : Sheaf (smallEtaleTopology (ofOver p.overObj)) AddCommGrpCat.{u}) :
    (abelianSectionsFunctor p).obj G = G.obj.obj (op p.sourceObj) :=
  sorry

/-- The geometric stalk of a sheaf of abelian groups at a geometric point, as inverse image along
the point morphism followed by sections over `Spec(k)`. -/
def abelianGeometricStalk (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})
    (xbar : GeometricPoint X) : AddCommGrpCat.{u} :=
  (abelianSectionsFunctor xbar.toFieldValuedPoint).obj
    ((sheafInverseImage AddCommGrpCat.{u} xbar.hom).obj F)

/-- The geometric stalk of a sheaf of abelian groups is inverse image along `xbar.hom`, then
sections over `Spec(k)`. -/
theorem abelianGeometricStalk_eq (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})
    (xbar : GeometricPoint X) :
    abelianGeometricStalk F xbar =
      (abelianSectionsFunctor xbar.toFieldValuedPoint).obj
        ((sheafInverseImage AddCommGrpCat.{u} xbar.hom).obj F) :=
  sorry

/-- Whether the geometric stalk of a sheaf of abelian groups is zero depends only on the image
point in `|X|`. -/
theorem abelianGeometricStalk_isZero_iff_of_image_eq
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) (xbar tbar : GeometricPoint X)
    (himage : xbar.image = tbar.image) :
    IsZero (abelianGeometricStalk F xbar) ↔ IsZero (abelianGeometricStalk F tbar) :=
  sorry

/-- The support of a sheaf of abelian groups on the small étale site, as the points of `|X|`
admitting a geometric point whose geometric stalk is a nonzero abelian group. -/
def abelianSheafSupport (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) : Set (Points X) :=
  {x | ∃ xbar : GeometricPoint X, xbar.image = x ∧ ¬ IsZero (abelianGeometricStalk F xbar)}

/-- Membership in the support of a sheaf of abelian groups is existence of a geometric point
over the point at which the geometric stalk is nonzero. -/
theorem mem_abelianSheafSupport_iff (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})
    (x : Points X) :
    x ∈ abelianSheafSupport F ↔
      ∃ xbar : GeometricPoint X, xbar.image = x ∧ ¬ IsZero (abelianGeometricStalk F xbar) :=
  sorry

namespace Modules

/-- The support of an `𝒪_X`-module is the support of its underlying abelian sheaf on the small
étale site. -/
abbrev moduleSupport (F : X.Modules) : Set (Points X) :=
  abelianSheafSupport ((SheafOfModules.toSheaf (structureSheaf X)).obj F)

/-- Membership in the support of an `𝒪_X`-module is existence of a geometric point over the
point at which the geometric stalk of the underlying abelian sheaf is nonzero. -/
theorem mem_moduleSupport_iff (F : X.Modules) (x : Points X) :
    x ∈ moduleSupport F ↔
      ∃ xbar : GeometricPoint X, xbar.image = x ∧
        ¬ IsZero (abelianGeometricStalk
            ((SheafOfModules.toSheaf (structureSheaf X)).obj F) xbar) :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
