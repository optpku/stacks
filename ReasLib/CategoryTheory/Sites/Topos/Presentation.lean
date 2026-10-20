/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.LeftExact
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom
public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentations of morphisms of topoi

This module owns the site-level presentation of a morphism of topoi by its
values on sheafified representables.  It is independent of a numbered chapter.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace MorphismOfTopoiIn

/-- The sheaf-valued functor induced by a morphism of topoi on sheafified
representables. -/
noncomputable abbrev presentation
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K) :
    C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) :=
  GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₂ v₂, v₁, u₁} J ⋙
    f.inverseImageFunctor.obj

namespace Presentation

/-- The Hom-presheaf on `C` associated to a sheaf-valued functor and a target sheaf. -/
abbrev homPresheaf
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    Cᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂)) :=
  Φ.op ⋙ yoneda.obj F

/-- The object part of the direct image reconstructed from a sheaf-valued
functor presentation. -/
noncomputable abbrev directImageObj
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (hΦ : ∀ F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))),
      Presheaf.IsSheaf J (homPresheaf Φ F))
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) :=
  ⟨homPresheaf Φ F, hΦ F⟩

/-- The morphism part of the direct image reconstructed from a sheaf-valued
functor presentation. -/
noncomputable abbrev directImageMap
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (hΦ : ∀ F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))),
      Presheaf.IsSheaf J (homPresheaf Φ F))
    {F G : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))} (η : F ⟶ G) :
    directImageObj Φ hΦ F ⟶ directImageObj Φ hΦ G :=
  Sheaf.homEquiv.symm (Functor.whiskerLeft Φ.op (yoneda.map η))

/-- The reconstructed direct image preserves identities. -/
theorem directImageMap_id
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (hΦ : ∀ F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))),
      Presheaf.IsSheaf J (homPresheaf Φ F))
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    directImageMap Φ hΦ (𝟙 F) = 𝟙 (directImageObj Φ hΦ F) := sorry

/-- The reconstructed direct image preserves composition. -/
theorem directImageMap_comp
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (hΦ : ∀ F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))),
      Presheaf.IsSheaf J (homPresheaf Φ F))
    {F G H : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))} (η : F ⟶ G) (θ : G ⟶ H) :
    directImageMap Φ hΦ (η ≫ θ) = directImageMap Φ hΦ η ≫ directImageMap Φ hΦ θ := sorry

/-- The direct-image functor reconstructed from a sheaf-valued functor
presentation. -/
noncomputable def directImage
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (hΦ : ∀ F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))),
      Presheaf.IsSheaf J (homPresheaf Φ F)) :
    Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤
      Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) where
  obj F := directImageObj Φ hΦ F
  map η := directImageMap Φ hΦ η
  map_id := directImageMap_id Φ hΦ
  map_comp := directImageMap_comp Φ hΦ

/-- Remark 7.15.4 (00XB): a sheaf-valued functor presents a morphism of topoi
when its Hom-presheaves are sheaves and the resulting direct image has a
left-exact left adjoint. -/
@[stacks 00XB]
class Presents
    (J : GrothendieckTopology C)
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) where
  /-- Every target Hom-presheaf is a sheaf on the source site. -/
  homSheaf (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    Presheaf.IsSheaf J (homPresheaf Φ F)
  /-- The left-exact inverse-image functor supplied by the presentation. -/
  inverseImage :
    Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤ₗ
      Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))
  /-- The inverse image is left adjoint to the reconstructed direct image. -/
  adjunction : inverseImage.obj ⊣ directImage Φ homSheaf

namespace Presents

/-- A presentation reconstructs its corresponding morphism of topoi. -/
noncomputable def toMorphism
    {Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))}
    (hΦ : Presents J Φ) :
    MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K :=
  { inverseImageFunctor := hΦ.inverseImage
    pushforward := directImage Φ hΦ.homSheaf
    adjunction := hΦ.adjunction }

end Presents

/-- The objectwise Hom-set comparison for the canonical presentation of a
morphism of topoi. -/
noncomputable def homComponent
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) (U : Cᵒᵖ) :
    (f.presentation.op ⋙ yoneda.obj F).obj U ≅ ((f.pushforward).obj F).obj.obj U :=
  Equiv.toIso <|
    (f.adjunction.homEquiv
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, v₁, u₁} J U.unop) F).trans
      ((GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
        ((f.pushforward).obj F) U.unop).trans
        (Equiv.refl _))

/-- The canonical Hom-set comparisons are natural in the site object. -/
theorem homComponent_naturality
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) {U V : Cᵒᵖ} (g : U ⟶ V) :
    (f.presentation.op ⋙ yoneda.obj F).map g ≫ (homComponent f F V).hom =
      (homComponent f F U).hom ≫ ((f.pushforward).obj F).obj.map g := sorry

/-- The Hom-presheaf of the canonical presentation is naturally isomorphic to
the presheaf underlying the original direct image. -/
noncomputable def homIso
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    f.presentation.op ⋙ yoneda.obj F ≅ ((f.pushforward).obj F).obj :=
  NatIso.ofComponents (homComponent f F) (homComponent_naturality f F)

/-- Every Hom-presheaf of the canonical presentation is a sheaf. -/
theorem homSheaf
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    Presheaf.IsSheaf J (f.presentation.op ⋙ yoneda.obj F) := sorry

/-- The direct-image object reconstructed from the canonical presentation is
isomorphic to the original direct-image object. -/
noncomputable def directImageObjIso
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    directImageObj f.presentation (homSheaf f) F ≅ (f.pushforward).obj F :=
  Functor.FullyFaithful.preimageIso
    (CategoryTheory.fullyFaithfulSheafToPresheaf J (Type (max (max u₁ v₁) (max u₂ v₂))))
    (homIso f F)

/-- The reconstructed direct-image object comparisons are natural in target
sheaves. -/
theorem directImageObjIso_naturality
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    {F G : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))} (η : F ⟶ G) :
    (directImage f.presentation (homSheaf f)).map η ≫ (directImageObjIso f G).hom =
      (directImageObjIso f F).hom ≫ (f.pushforward).map η := sorry

/-- The direct image reconstructed from the canonical presentation is naturally
isomorphic to the original direct image. -/
noncomputable def directImageIso
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K) :
    directImage f.presentation (homSheaf f) ≅ f.pushforward :=
  NatIso.ofComponents (directImageObjIso f) (directImageObjIso_naturality f)

/-- The canonical presentation of a morphism of topoi satisfies the presentation
conditions. -/
noncomputable instance presents
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K) :
    Presents J f.presentation where
  homSheaf := homSheaf f
  inverseImage := f.inverseImageFunctor
  adjunction := f.adjunction.ofNatIsoRight (directImageIso f).symm

end Presentation

end MorphismOfTopoiIn

end CategoryTheory
