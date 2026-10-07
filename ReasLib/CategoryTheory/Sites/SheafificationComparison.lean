module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Continuous sheafification comparisons

This leaf owns the comparison obtained from the universal property of
sheafification for a continuous functor of sites.  Unlike Mathlib's
`pushforwardContinuousSheafificationCompatibility`, it requires only
continuity; under additional cocontinuity hypotheses the two comparisons
agree.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [G.IsContinuous J K]

/-- A locally bijective map from a presheaf into a sheaf induces an isomorphism after
sheafification when the source sheafification unit is locally surjective. -/
theorem sheafifyLift_isIso_of_isLocallyBijective
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    [Presheaf.IsLocallySurjective J (toSheafify J P)]
    [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η] :
    IsIso (sheafifyLift J η hQ) := sorry

namespace Functor

/-- The comparison from sheafifying after precomposition along a continuous
functor to the continuous sheaf pushforward of a sheafified presheaf. -/
def continuousSheafificationComparison :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj G.op ⋙ presheafToSheaf J (Type w) ⟶
      presheafToSheaf K (Type w) ⋙ G.sheafPushforwardContinuous (Type w) J K where
  app F :=
    ObjectProperty.homMk <|
      sheafifyLift J
        (Functor.whiskerLeft G.op (toSheafify K F))
        ((presheafToSheaf K (Type w) ⋙ G.sheafPushforwardContinuous (Type w) J K).obj F).property
  naturality := sorry

/-- The continuous sheafification comparison is invertible when the functor
is also cocontinuous and admits the required pointwise right Kan extensions. -/
theorem continuousSheafificationComparison_isIso
    [G.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension F] :
    IsIso (G.continuousSheafificationComparison J K) := sorry

/-- Under cocontinuity and the right-Kan-extension hypotheses, the explicit
continuous sheafification comparison agrees componentwise with Mathlib's
canonical compatibility isomorphism. -/
theorem continuousSheafificationComparison_eq_compatibility_hom_app
    [G.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension F]
    (F : Dᵒᵖ ⥤ Type w) :
    (G.continuousSheafificationComparison J K).app F =
      (G.pushforwardContinuousSheafificationCompatibility (Type w) J K).hom.app F := sorry

end Functor

end CategoryTheory
