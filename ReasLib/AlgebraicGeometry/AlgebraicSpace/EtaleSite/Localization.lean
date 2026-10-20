module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction

/-!
# Étale localization of spaces-étale sites

An étale morphism `f : X ⟶ Y` of algebraic spaces identifies the spaces-étale site of `X`
with the localization of the spaces-étale site of `Y` at the object `spacesEtaleSite.mk f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The object of `Y_spaces,étale` associated to an étale morphism `f : X ⟶ Y`. -/
def spacesEtaleSite.mk (f : X ⟶ Y) [Etale f] : spacesEtaleSite Y :=
  MorphismProperty.Over.mk ⊤ f inferInstance

/-- The underlying algebraic space of `spacesEtaleSite.mk f` is the domain of `f`. -/
@[simp]
theorem spacesEtaleSite.mk_left (f : X ⟶ Y) [Etale f] :
    (spacesEtaleSite.mk f).left = X :=
  rfl

/-- The structural morphism of `spacesEtaleSite.mk f` is `f`. -/
@[simp]
theorem spacesEtaleSite.mk_hom (f : X ⟶ Y) [Etale f] :
    (spacesEtaleSite.mk f).hom = f :=
  rfl

/-- A morphism in the slice `Y_spaces,étale / X` remains étale over `X`. -/
instance etale_of_spacesEtaleSlice (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) :
    Etale (W.hom.left : W.left.left ⟶ X) :=
  sorry

/-- The morphism in `Y_spaces,étale` from the postcomposition of `V` with `f` to `f` itself. -/
def spacesEtaleLocalizationHom (f : X ⟶ Y) [Etale f] (V : spacesEtaleSite X) :
    (spacesEtaleRestriction f).obj V ⟶ spacesEtaleSite.mk f :=
  MorphismProperty.Over.homMk V.hom (by rfl)

/-- The underlying morphism of algebraic spaces of `spacesEtaleLocalizationHom` is the structure
morphism of `V`. -/
@[simp]
theorem spacesEtaleLocalizationHom_left (f : X ⟶ Y) [Etale f] (V : spacesEtaleSite X) :
    (spacesEtaleLocalizationHom f V).left = V.hom :=
  rfl

/-- Postcomposition with `f` is a morphism over `spacesEtaleSite.mk f`. -/
theorem spacesEtaleLocalizationHom_naturality (f : X ⟶ Y) [Etale f]
    {V W : spacesEtaleSite X} (g : V ⟶ W) :
    (spacesEtaleRestriction f).map g ≫ spacesEtaleLocalizationHom f W =
      spacesEtaleLocalizationHom f V :=
  sorry

/-- The site functor `X_spaces,étale ⥤ Y_spaces,étale / X` for an étale morphism of algebraic
spaces. -/
def spacesEtaleLocalizationFunctor (f : X ⟶ Y) [Etale f] :
    spacesEtaleSite X ⥤ Over (spacesEtaleSite.mk f) :=
  (spacesEtaleRestriction f).toOver (spacesEtaleSite.mk f) (spacesEtaleLocalizationHom f)
    (spacesEtaleLocalizationHom_naturality f)

/-- The object of `X_spaces,étale` associated to a slice object over `f`. -/
def spacesEtaleLocalizationInverseObj (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) : spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (W.hom.left : W.left.left ⟶ X)
    (etale_of_spacesEtaleSlice f W)

/-- The inverse site functor `Y_spaces,étale / X ⥤ X_spaces,étale`, sending a slice object to the
corresponding étale morphism of algebraic spaces over `X`. -/
def spacesEtaleLocalizationInverse (f : X ⟶ Y) [Etale f] :
    Over (spacesEtaleSite.mk f) ⥤ spacesEtaleSite X where
  obj := spacesEtaleLocalizationInverseObj f
  map g := MorphismProperty.Over.homMk g.left.left
    (by exact congrArg (fun k ↦ k.left) (Over.w g))
  map_id _ := by apply MorphismProperty.Over.Hom.ext; rfl
  map_comp _ _ := by apply MorphismProperty.Over.Hom.ext; rfl

/-- The inverse object is the étale object constructed from the underlying slice arrow. -/
@[simp]
theorem spacesEtaleLocalizationInverseObj_eq (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) :
    spacesEtaleLocalizationInverseObj f W =
      MorphismProperty.Over.mk ⊤ (W.hom.left : W.left.left ⟶ X)
        (etale_of_spacesEtaleSlice f W) :=
  rfl

/-- On objects, `spacesEtaleLocalizationInverse` is `spacesEtaleLocalizationInverseObj`. -/
@[simp]
theorem spacesEtaleLocalizationInverse_obj (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) :
    (spacesEtaleLocalizationInverse f).obj W = spacesEtaleLocalizationInverseObj f W :=
  rfl

/-- The underlying algebraic space of an inverse-image object is the domain of the slice
object. -/
@[simp]
theorem spacesEtaleLocalizationInverse_obj_left (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) :
    ((spacesEtaleLocalizationInverse f).obj W).left = W.left.left :=
  rfl

/-- The structure morphism of an inverse-image object is the underlying slice arrow. -/
@[simp]
theorem spacesEtaleLocalizationInverse_obj_hom (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) :
    ((spacesEtaleLocalizationInverse f).obj W).hom = W.hom.left :=
  rfl

/-- The unit of spaces-étale localization, identifying an étale space over `X` with the
corresponding slice object over `f`. -/
def spacesEtaleLocalizationUnitIso (f : X ⟶ Y) [Etale f] :
    𝟭 (spacesEtaleSite X) ≅
      spacesEtaleLocalizationFunctor f ⋙ spacesEtaleLocalizationInverse f :=
  NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _) (by exact Category.id_comp V.hom))
    (by
      intro V W g
      apply MorphismProperty.Over.Hom.ext
      change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
      simp only [Category.comp_id, Category.id_comp])

/-- The counit of spaces-étale localization, identifying a slice object over `f` with the
postcomposition of its underlying étale morphism. -/
def spacesEtaleLocalizationCounitIso (f : X ⟶ Y) [Etale f] :
    spacesEtaleLocalizationInverse f ⋙ spacesEtaleLocalizationFunctor f ≅
      𝟭 (Over (spacesEtaleSite.mk f)) :=
  NatIso.ofComponents
    (fun W ↦ Over.isoMk
      (MorphismProperty.Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ W.left.hom = W.hom.left ≫ f
        exact (Category.id_comp _).trans (MorphismProperty.Over.w W.hom).symm))
      (by
        apply MorphismProperty.Over.Hom.ext
        change 𝟙 _ ≫ W.hom.left = W.hom.left
        exact Category.id_comp _))
    (by
      intro V W g
      apply Over.OverMorphism.ext
      apply MorphismProperty.Over.Hom.ext
      change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
      simp only [Category.comp_id, Category.id_comp])

/-- Identification of sites `X_spaces,étale = Y_spaces,étale / X` along an étale morphism of
algebraic spaces, as an equivalence with the localization of `Y_spaces,étale` at
`spacesEtaleSite.mk f`. -/
def spacesEtaleLocalizationEquivalence (f : X ⟶ Y) [Etale f] :
    spacesEtaleSite X ≌ Over (spacesEtaleSite.mk f) :=
  CategoryTheory.Equivalence.mk (spacesEtaleLocalizationFunctor f)
    (spacesEtaleLocalizationInverse f) (spacesEtaleLocalizationUnitIso f)
    (spacesEtaleLocalizationCounitIso f)

/-- The forward functor of the spaces-étale localization equivalence is
`spacesEtaleLocalizationFunctor`. -/
@[simp]
theorem spacesEtaleLocalizationEquivalence_functor (f : X ⟶ Y) [Etale f] :
    (spacesEtaleLocalizationEquivalence f).functor = spacesEtaleLocalizationFunctor f :=
  rfl

/-- The inverse functor of the spaces-étale localization equivalence is
`spacesEtaleLocalizationInverse`. -/
@[simp]
theorem spacesEtaleLocalizationEquivalence_inverse (f : X ⟶ Y) [Etale f] :
    (spacesEtaleLocalizationEquivalence f).inverse = spacesEtaleLocalizationInverse f :=
  rfl

/-- `spacesEtaleLocalizationFunctor` is continuous from `X_spaces,étale` to the slice topology on
`Y_spaces,étale / X`. -/
instance spacesEtaleLocalizationFunctor.instIsContinuous (f : X ⟶ Y) [Etale f] :
    (spacesEtaleLocalizationFunctor f).IsContinuous (spacesEtaleTopology X)
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f)) :=
  sorry

/-- `spacesEtaleLocalizationFunctor` is cocontinuous from `X_spaces,étale` to the slice topology on
`Y_spaces,étale / X`. -/
instance spacesEtaleLocalizationFunctor.instIsCocontinuous (f : X ⟶ Y) [Etale f] :
    (spacesEtaleLocalizationFunctor f).IsCocontinuous (spacesEtaleTopology X)
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f)) :=
  sorry

/-- `spacesEtaleLocalizationFunctor` is a morphism of sites from the slice `Y_spaces,étale / X` to
`X_spaces,étale`. -/
instance spacesEtaleLocalizationFunctor.instIsMorphismOfSites (f : X ⟶ Y) [Etale f] :
    IsMorphismOfSites (spacesEtaleTopology X)
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
      (spacesEtaleLocalizationFunctor f) :=
  sorry

/-- `spacesEtaleLocalizationInverse` is continuous from the slice `Y_spaces,étale / X` to
`X_spaces,étale`. -/
instance spacesEtaleLocalizationInverse.instIsContinuous (f : X ⟶ Y) [Etale f] :
    (spacesEtaleLocalizationInverse f).IsContinuous
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f)) (spacesEtaleTopology X) :=
  sorry

/-- `spacesEtaleLocalizationInverse` is cocontinuous from the slice `Y_spaces,étale / X` to
`X_spaces,étale`. -/
instance spacesEtaleLocalizationInverse.instIsCocontinuous (f : X ⟶ Y) [Etale f] :
    (spacesEtaleLocalizationInverse f).IsCocontinuous
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f)) (spacesEtaleTopology X) :=
  sorry

/-- `spacesEtaleLocalizationInverse` is a morphism of sites from `X_spaces,étale` to the slice
`Y_spaces,étale / X`. -/
instance spacesEtaleLocalizationInverse.instIsMorphismOfSites (f : X ⟶ Y) [Etale f] :
    IsMorphismOfSites ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
      (spacesEtaleTopology X) (spacesEtaleLocalizationInverse f) :=
  sorry

/-- Forgetting the slice recovers spaces-étale restriction. -/
def spacesEtaleLocalizationFunctor_comp_forget (f : X ⟶ Y) [Etale f] :
    spacesEtaleLocalizationFunctor f ⋙ Over.forget (spacesEtaleSite.mk f) ≅
      spacesEtaleRestriction f :=
  (spacesEtaleRestriction f).toOverCompForget (spacesEtaleSite.mk f)
    (spacesEtaleLocalizationHom f) (spacesEtaleLocalizationHom_naturality f)

end AlgebraicGeometry.AlgebraicSpace
