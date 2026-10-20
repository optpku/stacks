module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Constant sheaves and continuous, cocontinuous restriction

For a functor `G : C ⥤ D` that is continuous and cocontinuous, restriction
`G.sheafPushforwardContinuous` of the constant sheaf with coefficients `E` is the
constant sheaf with coefficients `E` (Stacks, Sites, section `section-localize`).
This is the canonical owner of that fact: `constantSheafRestrictionIso` is the
natural isomorphism whose component at `E` is the native compatibility
`G.pushforwardContinuousSheafificationCompatibility` between restriction and
sheafification at the constant presheaf. The slice case `G = Over.forget U`
(restriction of a constant sheaf to `D/U`) is the instance of the same iso.

The right Kan extension followed by global sections is the original
global-section functor, recorded by `sheafPushforwardCocontinuousCompGlobalSectionsIso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section
universe u₀ u₁ v₀ v₁ u₂ v₂

namespace CategoryTheory.Functor

variable {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
variable (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (A : Type u₂) [Category.{v₂} A]
variable [G.IsContinuous J K] [G.IsCocontinuous J K]
variable [HasWeakSheafify J A] [HasWeakSheafify K A]
variable [∀ P : Cᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]

/-- Restriction along a continuous and cocontinuous functor sends the constant sheaf
with coefficients `E` to the constant sheaf with coefficients `E`; the component at `E`
is the native restriction/sheafification compatibility at the constant presheaf. -/
def constantSheafRestrictionIso :
    constantSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅ constantSheaf J A :=
  NatIso.ofComponents
    (fun E ↦ (G.pushforwardContinuousSheafificationCompatibility A J K).symm.app
      ((Functor.const Dᵒᵖ).obj E))
    (fun f ↦ (G.pushforwardContinuousSheafificationCompatibility A J K).inv.naturality
      ((Functor.const Dᵒᵖ).map f))

/-- The component of `constantSheafRestrictionIso` at a coefficient object. -/
theorem constantSheafRestrictionIso_app (E : A) :
    (G.constantSheafRestrictionIso J K A).app E =
      (G.pushforwardContinuousSheafificationCompatibility A J K).symm.app
        ((Functor.const Dᵒᵖ).obj E) :=
  rfl

variable [HasLimitsOfShape Cᵒᵖ A] [HasLimitsOfShape Dᵒᵖ A]

/-- The actual right Kan extension preserves global sections by its limit comparison. -/
def sheafPushforwardCocontinuousCompGlobalSectionsIso :
    G.sheafPushforwardCocontinuous A J K ⋙ Sheaf.Γ K A ≅ Sheaf.Γ J A :=
  isoWhiskerLeft (G.sheafPushforwardCocontinuous A J K) (Sheaf.ΓNatIsoLim K A) ≪≫
    (Functor.associator (G.sheafPushforwardCocontinuous A J K)
      (sheafToPresheaf K A) lim).symm ≪≫
    isoWhiskerRight (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K) lim ≪≫
    Functor.associator (sheafToPresheaf J A) G.op.ran lim ≪≫
    isoWhiskerLeft (sheafToPresheaf J A) (G.op.ranCompLimIso) ≪≫
    (Sheaf.ΓNatIsoLim J A).symm

end CategoryTheory.Functor
