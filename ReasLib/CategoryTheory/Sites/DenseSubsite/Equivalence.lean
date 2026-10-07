module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Dense-subsite equivalences on sheaves

The dense-subsite comparison theorem in mathlib supplies the core equivalence. This module owns
the cocontinuous-pushforward formulation used by applications with chosen pointwise right Kan
extensions.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor.IsDenseSubsite

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Definition 7.29.2: under the required pointwise right Kan extensions, the cocontinuous
pushforward of a dense subsite is an equivalence on `Type w`-valued sheaves. -/
theorem sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
    (G : C ⥤ D) [G.IsDenseSubsite J K]
    [forall P : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension P] :
    (G.sheafPushforwardCocontinuous (Type w) J K).IsEquivalence := sorry

/-- The set-valued cocontinuous pushforward of a dense subsite is an equivalence when all
required pointwise right Kan extensions exist. -/
instance sheafPushforwardCocontinuous_isEquivalence
    (G : C ⥤ D) [G.IsDenseSubsite J K]
    [forall P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), G.op.HasPointwiseRightKanExtension P] :
    (G.sheafPushforwardCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).IsEquivalence := sorry

end CategoryTheory.Functor.IsDenseSubsite
