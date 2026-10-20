module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ExtensionByZero

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u u₁ v₁

namespace AlgebraicGeometry.Scheme

namespace ProEt

variable {U X : Scheme.{u}}

/-- Direct image of sheaves along a weakly étale morphism, given by the
cocontinuous sheaf pushforward of pro-étale restriction. -/
abbrev directImage (j : U ⟶ X) [WeaklyEtale j] (A : Type u₁) [Category.{v₁} A]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F] :
    Sheaf (topology U) A ⥤ Sheaf (topology X) A :=
  (restriction j).sheafPushforwardCocontinuous A (topology U) (topology X)

/-- The canonical adjunction for pro-étale restriction and direct image. -/
def directImage_adjunction (j : U ⟶ X) [WeaklyEtale j]
    (A : Type u₁) [Category.{v₁} A]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F] :
    restrictionSheaf j A ⊣ directImage j A :=
  (restriction j).sheafAdjunctionCocontinuous A (topology U) (topology X)

end ProEt

end AlgebraicGeometry.Scheme
