module

public import ReasLib.CategoryTheory.Sites.Pushforward.SmallSectionsAdjunction

/-!
# Ring sheaf direct image from small underlying sheaf sections

The size condition for type-valued sheaves applies to the actual underlying
sheaf of a ring sheaf. Both the adjunction and forget comparison then use
the real per-diagram native pointwise extension maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe uC vC uD vD w

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

variable (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [G.IsCocontinuous J K] [G.IsContinuous J K]
variable [J.HasSheafCompose (forget RingCat.{w})]
variable [K.HasSheafCompose (forget RingCat.{w})]
variable [∀ F : Sheaf J (Type w), ∀ Y : Dᵒᵖ,
  Small.{w} (StructuredArrow.proj Y G.op ⋙ F.obj).sections]

/-- The actual underlying type-valued sheaf supplies size for every ring sheaf diagram. -/
instance ringSheafSectionSmall (F : Sheaf J RingCat.{w}) (Y : Dᵒᵖ) :
    Small.{w} ((StructuredArrow.proj Y G.op ⋙ F.obj) ⋙ forget RingCat.{w}).sections :=
  inferInstanceAs
    (Small.{w} (StructuredArrow.proj Y G.op ⋙
      ((sheafCompose J (forget RingCat.{w})).obj F).obj).sections)

/-- Ring transposition keeps the actual counit and native pointwise universal lift. -/
def sheafPushforwardRingOfSmallSectionsHomEquiv
    (F : Sheaf J RingCat.{w}) (N : Sheaf K RingCat.{w}) :
    (N ⟶ (sheafPushforwardRingOfSmallSections G J K).obj F) ≃
      ((G.sheafPushforwardContinuous RingCat.{w} J K).obj N ⟶ F) where
  toFun η := ObjectProperty.homMk
    (whiskerLeft G.op η.hom ≫ pointwiseRightKanExtensionCounit G.op F.obj)
  invFun η := ObjectProperty.homMk
    ((pointwiseRightKanExtension G.op F.obj).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit G.op F.obj) N.obj η.hom)
  left_inv := sorry
  right_inv := sorry

def sheafPushforwardRingOfSmallSectionsAdjunction :
    G.sheafPushforwardContinuous RingCat.{w} J K ⊣ sheafPushforwardRingOfSmallSections G J K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N F ↦ (sheafPushforwardRingOfSmallSectionsHomEquiv G J K F N).symm
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- Forgetting rings compares the actual per-sheaf Kan extensions with native hom and inv maps. -/
def sheafPushforwardRingOfSmallSectionsForgetIso :
    sheafPushforwardRingOfSmallSections G J K ⋙ sheafCompose K (forget RingCat.{w}) ≅
      sheafCompose J (forget RingCat.{w}) ⋙ sheafPushforwardOfSmallSections G J K :=
  NatIso.ofComponents
    (fun F ↦
      { hom := ObjectProperty.homMk
          ((forget RingCat.{w}).pointwiseRightKanExtensionCompIsoOfPreserves F.obj G.op).hom
        inv := ObjectProperty.homMk
          ((forget RingCat.{w}).pointwiseRightKanExtensionCompIsoOfPreserves F.obj G.op).inv
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

end CategoryTheory.Functor
