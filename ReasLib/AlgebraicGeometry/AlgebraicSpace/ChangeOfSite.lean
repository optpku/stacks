module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Pullback

/-!
# Inverse image along an enlargement of big sites

A fully faithful continuous functor of sites induces an inverse-image functor on slices. Representable sheaves are sent to the Yoneda
sheaf of the same object in the larger slice, and an algebraic space on the smaller
slice yields an algebraic space on `Over (u.obj X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u v uC uD

namespace AlgebraicGeometry.AlgebraicSpace

variable {C : Type uC} {D : Type uD} [Category.{v} C] [Category.{v} D]
variable (u : C ⥤ D) (X : C)

/-- The slice functor `Over X ⥤ Over (u.obj X)` induced by a functor of sites. -/
abbrev slicePost : Over X ⥤ Over (u.obj X) :=
  Over.post u

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [(slicePost u X).IsContinuous (J.over X) (K.over (u.obj X))]
variable [HasWeakSheafify (K.over (u.obj X)) (Type v)]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type v, (slicePost u X).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost u X).sheafPullback (Type v) (J.over X) (K.over (u.obj X)))]

/-- The left Kan extension of `yoneda.obj U` along `(slicePost u X).op` is the Yoneda
presheaf of the image object. -/
def lanYonedaIso (U : Over X) :
    (slicePost u X).op.lan.obj (yoneda.obj U) ≅
      yoneda.obj ((slicePost u X).obj U) :=
  Functor.mapIso (slicePost u X).op.lan
      ((uliftYonedaIsoYoneda.{v} (C := Over X)).symm.app U) ≪≫
    ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{v} (slicePost u X)).app U).symm ≪≫
    (uliftYonedaIsoYoneda.{v} (C := Over (u.obj X))).app ((slicePost u X).obj U)

/-- Inverse image of sheaves of sets along the slice functor of a continuous functor of
sites, given by sheaf pullback on the slice categories. -/
abbrev inverseImage :
    Sheaf (J.over X) (Type v) ⥤ Sheaf (K.over (u.obj X)) (Type v) :=
  (slicePost u X |>.morphismOfTopoiInOfContinuous (J.over X) (K.over (u.obj X)))⁻¹

/-- Slice inverse image is sheaf pullback along `slicePost u X`. -/
theorem inverseImage_eq_sheafPullback :
    inverseImage u X J K =
      (slicePost u X).sheafPullback (Type v) (J.over X) (K.over (u.obj X)) := rfl

variable [J.Subcanonical] [K.Subcanonical]

/-- The comparison identifying the inverse image of a representable sheaf on `Over X` with
the Yoneda sheaf of the same object in the larger slice. -/
def inverseImageYonedaIso [u.Full] [u.Faithful] (U : Over X) :
    (inverseImage u X J K).obj ((J.over X).yoneda.obj U) ≅
      (K.over (u.obj X)).yoneda.obj ((slicePost u X).obj U) :=
  (Functor.sheafPullbackConstruction.sheafPullbackIso
        (slicePost u X) (Type v) (J.over X) (K.over (u.obj X))).app
        ((J.over X).yoneda.obj U) ≪≫
      (presheafToSheaf (K.over (u.obj X)) (Type v)).mapIso
        (lanYonedaIso u X U) ≪≫
      (sheafificationIso
        ((K.over (u.obj X)).yoneda.obj ((slicePost u X).obj U))).symm

/-- The forward comparison map `f⁻¹ h_U ⟶ h'_U`. -/
def inverseImageYonedaHom [u.Full] [u.Faithful] (U : Over X) :
    (inverseImage u X J K).obj ((J.over X).yoneda.obj U) ⟶
      (K.over (u.obj X)).yoneda.obj ((slicePost u X).obj U) :=
  (inverseImageYonedaIso u X J K U).hom

/-- The reverse comparison map `h'_U ⟶ f⁻¹ h_U`. -/
def inverseImageYonedaInv [u.Full] [u.Faithful] (U : Over X) :
    (K.over (u.obj X)).yoneda.obj ((slicePost u X).obj U) ⟶
      (inverseImage u X J K).obj ((J.over X).yoneda.obj U) :=
  (inverseImageYonedaIso u X J K U).inv

/-- The forward comparison of `inverseImageYonedaIso` is `inverseImageYonedaHom`. -/
theorem inverseImageYonedaIso_hom [u.Full] [u.Faithful] (U : Over X) :
    (inverseImageYonedaIso u X J K U).hom = inverseImageYonedaHom u X J K U := rfl

/-- The forward comparison `f⁻¹ h_U ⟶ h'_U` is an isomorphism. -/
instance inverseImageYonedaHom_isIso [u.Full] [u.Faithful] (U : Over X) :
    IsIso (inverseImageYonedaHom u X J K U) :=
  Iso.isIso_hom (inverseImageYonedaIso u X J K U)

/-- The atlas morphism of a small-site sheaf, transported to the larger slice by
inverse image and the Yoneda comparison. -/
def inverseImageAtlasHom [u.Full] [u.Faithful] {U₀ : Over X}
    {F : Sheaf (J.over X) (Type v)}
    (p : yoneda.obj U₀ ⟶ F.obj) :
    yoneda.obj ((slicePost u X).obj U₀) ⟶ ((inverseImage u X J K).obj F).obj :=
  ((inverseImageYonedaIso u X J K U₀).inv ≫
    (inverseImage u X J K).map (Sheaf.homEquiv.symm p)).hom

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (X : C)
variable [J.Subcanonical]
variable [(slicePost ι X).IsContinuous (J.over X) (Scheme.fppfTopology.over (ι.obj X))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj X)) (Type u)]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type u, (slicePost ι X).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι X).sheafPullback (Type u) (J.over X)
    (Scheme.fppfTopology.over (ι.obj X)))]
variable (F : Sheaf (J.over X) (Type u))

open Functor.relativelyRepresentable

/-- Inverse image along a fully faithful pullback-preserving enlargement of sites
preserves representability of the diagonal. -/
theorem inverseImage_representableDiagonal [ι.Full] [ι.Faithful]
    [PreservesLimitsOfShape WalkingCospan ι]
    (hdiag : yoneda.relativelyRepresentable (Limits.diag F.obj)) :
    yoneda.relativelyRepresentable
      (Limits.diag ((inverseImage ι X J Scheme.fppfTopology).obj F).obj) := sorry

/-- The inverse image of a representable atlas whose represented pullbacks are étale
is a representable étale morphism. -/
theorem inverseImageAtlasHom_etale [ι.Full] [ι.Faithful]
    [PreservesLimitsOfShape WalkingCospan ι]
    {U₀ : Over X} (p : yoneda.obj U₀ ⟶ F.obj)
    (hp : yoneda.relativelyRepresentable p)
    (hp_etale : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      (MorphismProperty.over (@Etale)) ((slicePost ι X).map (hp.snd ξ))) :
    (MorphismProperty.over (@Etale)).presheaf
      (inverseImageAtlasHom ι X J Scheme.fppfTopology p) := sorry

/-- An atlas with étale surjective represented pullbacks remains étale-locally
surjective after inverse image along an enlargement of sites. -/
theorem inverseImageAtlasHom_locallySurjective [ι.Full] [ι.Faithful]
    [PreservesLimitsOfShape WalkingCospan ι]
    {U₀ : Over X} (p : yoneda.obj U₀ ⟶ F.obj)
    (hp : yoneda.relativelyRepresentable p)
    (hp_etale : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      (MorphismProperty.over (@Etale)) ((slicePost ι X).map (hp.snd ξ)))
    (hp_surj : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      Surjective ((slicePost ι X).map (hp.snd ξ)).left) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (ι.obj X))
      (inverseImageAtlasHom ι X J Scheme.fppfTopology p) := sorry

/-- The algebraic space over `ι.obj X` obtained by inverse image of a sheaf that is an
algebraic space on the smaller site along a fully faithful continuous, pullback-preserving
enlargement of big sites. -/
def ofInverseImage [ι.Full] [ι.Faithful]
    [PreservesLimitsOfShape WalkingCospan ι]
    (hdiag : yoneda.relativelyRepresentable (Limits.diag F.obj))
    {U₀ : Over X} (p : yoneda.obj U₀ ⟶ F.obj)
    (hp : yoneda.relativelyRepresentable p)
    (hp_etale : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      (MorphismProperty.over (@Etale)) ((slicePost ι X).map (hp.snd ξ)))
    (hp_surj : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      Surjective ((slicePost ι X).map (hp.snd ξ)).left) :
    AlgebraicSpace (ι.obj X) :=
  ofFunctor ((inverseImage ι X J Scheme.fppfTopology).obj F).obj
    ((inverseImage ι X J Scheme.fppfTopology).obj F).property
    (inverseImage_representableDiagonal ι J X F hdiag)
    ⟨(slicePost ι X).obj U₀, inverseImageAtlasHom ι X J Scheme.fppfTopology p,
      inverseImageAtlasHom_etale ι J X F p hp hp_etale,
      inverseImageAtlasHom_locallySurjective ι J X F p hp hp_etale hp_surj⟩

/-- The functor of points of `ofInverseImage` is the underlying presheaf of the inverse
image sheaf. -/
@[simp]
theorem ofInverseImage_functorOfPoints [ι.Full] [ι.Faithful]
    [PreservesLimitsOfShape WalkingCospan ι]
    (hdiag : yoneda.relativelyRepresentable (Limits.diag F.obj))
    {U₀ : Over X} (p : yoneda.obj U₀ ⟶ F.obj)
    (hp : yoneda.relativelyRepresentable p)
    (hp_etale : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      (MorphismProperty.over (@Etale)) ((slicePost ι X).map (hp.snd ξ)))
    (hp_surj : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      Surjective ((slicePost ι X).map (hp.snd ξ)).left) :
    (ofInverseImage ι J X F hdiag p hp hp_etale hp_surj).functorOfPoints =
      ((inverseImage ι X J Scheme.fppfTopology).obj F).obj := rfl

/-- The inverse image of an algebraic-space sheaf is an fppf sheaf on the larger slice. -/
theorem ofInverseImage_isSheaf [ι.Full] [ι.Faithful]
    [PreservesLimitsOfShape WalkingCospan ι]
    (hdiag : yoneda.relativelyRepresentable (Limits.diag F.obj))
    {U₀ : Over X} (p : yoneda.obj U₀ ⟶ F.obj)
    (hp : yoneda.relativelyRepresentable p)
    (hp_etale : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      (MorphismProperty.over (@Etale)) ((slicePost ι X).map (hp.snd ξ)))
    (hp_surj : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      Surjective ((slicePost ι X).map (hp.snd ξ)).left) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (ι.obj X))
      (ofInverseImage ι J X F hdiag p hp hp_etale hp_surj).functorOfPoints :=
  (ofInverseImage ι J X F hdiag p hp hp_etale hp_surj).isSheaf

/-- The diagonal of the inverse-image algebraic space is representable by schemes. -/
theorem ofInverseImage_representableDiagonal [ι.Full] [ι.Faithful]
    [PreservesLimitsOfShape WalkingCospan ι]
    (hdiag : yoneda.relativelyRepresentable (Limits.diag F.obj))
    {U₀ : Over X} (p : yoneda.obj U₀ ⟶ F.obj)
    (hp : yoneda.relativelyRepresentable p)
    (hp_etale : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      (MorphismProperty.over (@Etale)) ((slicePost ι X).map (hp.snd ξ)))
    (hp_surj : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      Surjective ((slicePost ι X).map (hp.snd ξ)).left) :
    yoneda.relativelyRepresentable
      (Limits.diag (ofInverseImage ι J X F hdiag p hp hp_etale hp_surj).functorOfPoints) :=
  (ofInverseImage ι J X F hdiag p hp hp_etale hp_surj).representableDiagonal

/-- The transported atlas of `ofInverseImage` is the image scheme of `U₀` with comparison
`inverseImageAtlasHom p`; it is representable étale and étale-locally surjective. -/
theorem ofInverseImage_exists_atlas [ι.Full] [ι.Faithful]
    [PreservesLimitsOfShape WalkingCospan ι]
    (hdiag : yoneda.relativelyRepresentable (Limits.diag F.obj))
    {U₀ : Over X} (p : yoneda.obj U₀ ⟶ F.obj)
    (hp : yoneda.relativelyRepresentable p)
    (hp_etale : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      (MorphismProperty.over (@Etale)) ((slicePost ι X).map (hp.snd ξ)))
    (hp_surj : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
      Surjective ((slicePost ι X).map (hp.snd ξ)).left) :
    let U' : Over (ι.obj X) := (slicePost ι X).obj U₀
    let q : yoneda.obj U' ⟶ ((inverseImage ι X J Scheme.fppfTopology).obj F).obj :=
      inverseImageAtlasHom ι X J Scheme.fppfTopology p
    (MorphismProperty.over (@Etale)).presheaf q ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (ι.obj X)) q :=
  ⟨inverseImageAtlasHom_etale ι J X F p hp hp_etale,
    inverseImageAtlasHom_locallySurjective ι J X F p hp hp_etale hp_surj⟩

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- Inverse image along a scheme-compatible fully faithful enlargement of chosen big
fppf sites sends an algebraic-space sheaf to an algebraic-space sheaf. -/
theorem inverseImage_isAlgebraicSpace
    (𝒮 𝒯 : ChosenBigFppfSite.{u, v})
    (inclusion : 𝒮.carrier ⥤ 𝒯.carrier)
    (e : inclusion ⋙ 𝒯.toScheme ≅ 𝒮.toScheme) (S : 𝒮.carrier)
    [inclusion.Full] [inclusion.Faithful]
    [PreservesLimitsOfShape WalkingCospan inclusion]
    [(Over.post (X := S) inclusion).IsContinuous
      (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasWeakSheafify (𝒯.bigTopology (inclusion.obj S)) (Type (max u v))]
    [∀ P : (Over S)ᵒᵖ ⥤ Type (max u v),
      (Over.post (X := S) inclusion).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
        (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S)))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [HasPullbacks
      (Sheaf (𝒯.bigTopology (inclusion.obj S)) (Type (max u v)))]
    (F : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsAlgebraicSpace F] :
    IsAlgebraicSpace
      (((Over.post (X := S) inclusion).sheafPullback (Type (max u v))
        (𝒮.bigTopology S) (𝒯.bigTopology (inclusion.obj S))).obj F) := sorry

end AlgebraicGeometry.ChosenBigFppfSite
