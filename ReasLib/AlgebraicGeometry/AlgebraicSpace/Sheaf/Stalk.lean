module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Geometric
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage

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

/-- A factorization of geometric points induces an isomorphism of pullback-stalk functors. -/
theorem pullbackStalkFunctor_iso_of_factorization {p q : FieldValuedPoint X}
    [IsAlgClosed p.K] [IsAlgClosed q.K] (φ : Factorization p q)
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange p.hom).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology (ofOver p.overObj)) (Type (u + 1))]
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange q.hom).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology (ofOver q.overObj)) (Type (u + 1))] :
    Nonempty (p.pullbackStalkFunctor ≅ q.pullbackStalkFunctor) := sorry

/-- Let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`x` be a point of `|X|`. For any pair of geometric points `p` and `q` of `X` lying over `x`,
the stalk functors `Sh(X_étale) ⥤ Type` given by pullback along `p.hom` and along `q.hom`
are isomorphic.

By definition of `|X|` there is a third geometric point `p''` together with a commutative
triangle `p'' ⟶ p`, `p'' ⟶ q`, both over `X`. Since the stalk functor is pullback along the
geometric-point morphism, functoriality of pullback yields the isomorphism. -/
@[stacks 04K4]
theorem pullbackStalkFunctors_isomorphic (x : Points X) (p q : FieldValuedPoint X)
    [IsAlgClosed p.K] [IsAlgClosed q.K] (hp : Points.mk p = x) (hq : Points.mk q = x)
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange p.hom).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology (ofOver p.overObj)) (Type (u + 1))]
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange q.hom).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology (ofOver q.overObj)) (Type (u + 1))] :
    Nonempty (p.pullbackStalkFunctor ≅ q.pullbackStalkFunctor) := sorry

end AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint
