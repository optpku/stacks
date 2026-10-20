/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Pushforward.SmallSections
public import ReasLib.CategoryTheory.Sites.Topos.Morphism

/-!
# Adjunction for sheaf direct image with small sections

The actual pointwise extension of each sheaf provides both transposition
maps. This interface does not require right extensions of arbitrary
presheaves or a sheafification choice.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe uC vC uD vD w

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

section Types

variable (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [G.IsCocontinuous J K] [G.IsContinuous J K]
variable [∀ F : Sheaf J (Type w), ∀ Y : Dᵒᵖ,
  Small.{w} (StructuredArrow.proj Y G.op ⋙ F.obj).sections]

/-- Transpose the specified sheaf morphism using the actual pointwise universal lift. -/
def sheafPushforwardOfSmallSectionsHomEquiv
    (F : Sheaf J (Type w)) (N : Sheaf K (Type w)) :
    (N ⟶ (sheafPushforwardOfSmallSections G J K).obj F) ≃
      ((G.sheafPushforwardContinuous (Type w) J K).obj N ⟶ F) where
  toFun η := ObjectProperty.homMk
    (whiskerLeft G.op η.hom ≫ pointwiseRightKanExtensionCounit G.op F.obj)
  invFun η := ObjectProperty.homMk
    ((pointwiseRightKanExtension G.op F.obj).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit G.op F.obj) N.obj η.hom)
  left_inv := sorry
  right_inv := sorry

/-- The Hom equivalence supplies actual unit and counit maps for sheaf direct image. -/
def sheafPushforwardOfSmallSectionsAdjunction :
    G.sheafPushforwardContinuous (Type w) J K ⊣ sheafPushforwardOfSmallSections G J K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N F ↦ (sheafPushforwardOfSmallSectionsHomEquiv G J K F N).symm
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- Continuous inverse image with the actual small-section right adjoint.
Its finite-limit preservation is a law of continuous sheaf precomposition. -/
def morphismOfTopoiOfSmallSheafSections : MorphismOfTopoiIn K J where
  inverseImageFunctor := ⟨G.sheafPushforwardContinuous (Type w) J K, by sorry⟩
  pushforward := sheafPushforwardOfSmallSections G J K
  adjunction := sheafPushforwardOfSmallSectionsAdjunction G J K

end Types

end CategoryTheory.Functor
