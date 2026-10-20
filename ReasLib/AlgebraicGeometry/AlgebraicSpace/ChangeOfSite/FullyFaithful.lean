module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfSite
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Fully faithful enlargement of the site of algebraic spaces

The inverse-image functor for a scheme-compatible inclusion of chosen big fppf
sites restricts to algebraic spaces. Its essential image is described by two
locally surjective maps from objects of the smaller site.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- Algebraic spaces over a base in a chosen big fppf site form the full
subcategory of algebraic-space sheaves on its slice site. -/
abbrev Spaces (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))] :=
  ObjectProperty.FullSubcategory
    (IsAlgebraicSpace : ObjectProperty (Sheaf (𝒮.bigTopology S) (Type (max u v))))

variable (𝒮 𝒯 : ChosenBigFppfSite.{u, v})
variable (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
variable (e : inclusion ⋙ 𝒯.toScheme ≅ 𝒮.toScheme) (S : 𝒮.carrier)
variable [HasWeakSheafify (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))]
variable [HasPullbacks
  (Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v)))]

/-- A sheaf on the larger site admits smaller-site surjections if both it and
the self-fiber-product of one such cover are covered by sheafified
representables of smaller-site objects. -/
def HasSmallSiteSurjections
    (X' : Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))) : Prop :=
  ∃ (U R : 𝒮.bigSite S)
    (π : (𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentable
      ((Over.post inclusion).obj U) ⟶ X')
    (σ : (𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentable
      ((Over.post inclusion).obj R) ⟶ pullback π π),
    Sheaf.IsLocallySurjective π ∧ Sheaf.IsLocallySurjective σ

/-- The smaller-site surjection condition is exactly the existence of a
locally surjective cover and a locally surjective cover of its relation. -/
theorem hasSmallSiteSurjections_iff
    (X' : Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))) :
    HasSmallSiteSurjections 𝒮 𝒯 inclusion S X' ↔
      ∃ (U R : 𝒮.bigSite S)
        (π : (𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentable
          ((Over.post inclusion).obj U) ⟶ X')
        (σ : (𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentable
          ((Over.post inclusion).obj R) ⟶ pullback π π),
        Sheaf.IsLocallySurjective π ∧ Sheaf.IsLocallySurjective σ := Iff.rfl

/-- Relatively representable étale surjective maps from smaller-site objects
onto a sheaf and its covering relation satisfy the smaller-site surjection
condition. -/
theorem hasSmallSiteSurjections_of_etaleSurjective
    {X' : Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))}
    {U R : 𝒮.bigSite S}
    (π : (𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentable
      ((Over.post inclusion).obj U) ⟶ X')
    (σ : (𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentable
      ((Over.post inclusion).obj R) ⟶ pullback π π)
    (hπ : (MorphismProperty.inverseImage (@Etale ⊓ @Surjective)
      (𝒯.bigToScheme (inclusion.obj S))).relative
        (𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentableFunctor π)
    (hσ : (MorphismProperty.inverseImage (@Etale ⊓ @Surjective)
      (𝒯.bigToScheme (inclusion.obj S))).relative
        (𝒯.bigTopology (inclusion.obj S)).sheafifiedRepresentableFunctor σ) :
    HasSmallSiteSurjections 𝒮 𝒯 inclusion S X' := sorry

variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable [inclusion.Full] [inclusion.Faithful]
variable [PreservesLimitsOfShape WalkingCospan inclusion]
variable [(Over.post (X := S) inclusion).IsContinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
  (Over.post (X := S) inclusion).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
    (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)))]

/-- Inverse image along a scheme-compatible inclusion of chosen big fppf
sites, restricted to the full subcategories of algebraic spaces. -/
abbrev inverseImageFunctor : Spaces 𝒮 S ⥤ Spaces 𝒯 (inclusion.obj S) :=
  ObjectProperty.FullSubcategory.restrict
    ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
      (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)))
    (fun F hF ↦ inverseImage_isAlgebraicSpace 𝒮 𝒯 inclusion e S F)

/-- The underlying sheaf of the inverse image of an algebraic space is its
canonical sheaf pullback. -/
@[simp]
theorem inverseImageFunctor_obj_obj (X : Spaces 𝒮 S) :
    ((inverseImageFunctor 𝒮 𝒯 inclusion e S).obj X).obj =
      ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
        (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj X.obj := rfl

/-- The underlying morphism of inverse image is the canonical sheaf
pullback of the underlying morphism. -/
@[simp]
theorem inverseImageFunctor_map_hom {X Y : Spaces 𝒮 S} (f : X ⟶ Y) :
    ((inverseImageFunctor 𝒮 𝒯 inclusion e S).map f).hom =
      ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
        (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).map f.hom := rfl

variable [(Over.post (X := S) inclusion).IsCocontinuous
  (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
  (Over.post (X := S) inclusion).op.HasPointwiseLeftKanExtension P]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
  (Over.post (X := S) inclusion).op.HasPointwiseRightKanExtension P]

/-- An algebraic space on the larger site lies in the essential image of
inverse image exactly when it admits smaller-site surjections onto itself
and the self-fiber-product of a covering map. -/
theorem iso_ofInverseImage_iff (X' : Spaces 𝒯 (inclusion.obj S)) :
    (inverseImageFunctor 𝒮 𝒯 inclusion e S).essImage X' ↔
      HasSmallSiteSurjections 𝒮 𝒯 inclusion S X'.obj := sorry

/-- Enlarging a chosen big fppf site induces a fully faithful functor on
algebraic spaces, whose essential image is characterized by smaller-site
surjections onto the space and its covering relation. -/
theorem inverseImage_fullyFaithful_essImage :
    (inverseImageFunctor 𝒮 𝒯 inclusion e S).Full ∧
      (inverseImageFunctor 𝒮 𝒯 inclusion e S).Faithful ∧
      ∀ X' : Spaces 𝒯 (inclusion.obj S),
        (inverseImageFunctor 𝒮 𝒯 inclusion e S).essImage X' ↔
          HasSmallSiteSurjections 𝒮 𝒯 inclusion S X'.obj :=
  ⟨inferInstance, inferInstance, iso_ofInverseImage_iff 𝒮 𝒯 inclusion e S⟩

end AlgebraicGeometry.ChosenBigFppfSite
