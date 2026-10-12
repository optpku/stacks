/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

/-!
# Pullback presentation of étale stalks at field-valued points

The stalk functor of the small étale site of an algebraic space at a field-valued point is
presented as inverse image along the point morphism, followed by sections over the source
spectrum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The identity object `Spec(p.K)` of the small étale site of the source of a field-valued
point. -/
def sourceObj (p : FieldValuedPoint X) : smallEtaleSite (ofOver p.overObj) :=
  smallEtaleSite.mk (𝟙 (ofOver p.overObj))

/-- The source object is the identity morphism of `Spec(p.K)`, viewed in the small étale
site. -/
theorem sourceObj_eq (p : FieldValuedPoint X) :
    p.sourceObj = smallEtaleSite.mk (𝟙 (ofOver p.overObj)) := sorry

/-- Sections over `Spec(p.K)`, sending a sheaf on the small étale site of the source to its
value on the identity object. -/
def sectionsFunctor (p : FieldValuedPoint X) :
    Sheaf (smallEtaleTopology (ofOver p.overObj)) (Type (u + 1)) ⥤ Type (u + 1) :=
  sheafToPresheaf (smallEtaleTopology (ofOver p.overObj)) (Type (u + 1)) ⋙
    (evaluation (smallEtaleSite (ofOver p.overObj))ᵒᵖ (Type (u + 1))).obj (op p.sourceObj)

/-- Sections of a sheaf over the identity object of `Spec(p.K)`. -/
theorem sectionsFunctor_obj (p : FieldValuedPoint X)
    (G : Sheaf (smallEtaleTopology (ofOver p.overObj)) (Type (u + 1))) :
    (sectionsFunctor p).obj G = G.obj.obj (op p.sourceObj) := sorry

/-- The stalk functor at a field-valued point, as inverse image along the point morphism
followed by sections over `Spec(p.K)`. -/
def pullbackStalkFunctor (p : FieldValuedPoint X)
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange p.hom).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology (ofOver p.overObj)) (Type (u + 1))] :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1) :=
  sheafInverseImage (Type (u + 1)) p.hom ⋙ p.sectionsFunctor

/-- The pullback-stalk functor evaluates by inverse image, then sections over `Spec(p.K)`. -/
theorem pullbackStalkFunctor_obj (p : FieldValuedPoint X)
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange p.hom).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology (ofOver p.overObj)) (Type (u + 1))]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (pullbackStalkFunctor p).obj F =
      (sectionsFunctor p).obj ((sheafInverseImage (Type (u + 1)) p.hom).obj F) := sorry

end AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint
