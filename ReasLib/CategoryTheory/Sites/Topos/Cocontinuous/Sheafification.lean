module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cocontinuous pullback and sheafification

This leaf owns the comparison between sheafifying a presheaf after
precomposition and pulling back its sheafification along a cocontinuous
functor of sites.  It does not assume that the functor is continuous.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor.CocontinuousPullback

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

section

variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [G.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension F]

/-- Lemma 7.20.4 (00XM) (1): sheafification after presheaf pullback is canonically
isomorphic to cocontinuous sheaf pullback after sheafification. -/
@[stacks 00XM "(1)"]
noncomputable def sheafificationCompatibility :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj G.op ⋙
        presheafToSheaf J (Type w) ≅
      presheafToSheaf K (Type w) ⋙
        G.sheafPullbackCocontinuous (Type w) J K :=
  Adjunction.leftAdjointUniq
    ((G.op.ranAdjunction (Type w)).comp (sheafificationAdjunction J (Type w)))
    ((sheafificationAdjunction K (Type w)).comp
      (G.sheafPullbackCocontinuousAdjunction J K))

end

section

/-- Lemma 7.20.4 (00XM) (2): the concrete weak-sheafification map induced by
presheaf pullback along a cocontinuous functor is invertible. -/
@[stacks 00XM "(2)"]
instance sheafifyMap_isIso
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), G.op.HasPointwiseRightKanExtension F]
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    IsIso (J.sheafifyMap (whiskerLeft G.op (K.toSheafify F))) := sorry

end

end CategoryTheory.Functor.CocontinuousPullback
