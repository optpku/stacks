module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Zero morphisms for cocontinuous sheaf pullback

The sheafified pullback attached to a cocontinuous functor preserves zero
morphisms for preadditive coefficients.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Sheafified pullback with coefficients in a preadditive category preserves
zero morphisms. -/
instance sheafPullbackCocontinuous_preservesZeroMorphisms
    (G : C ⥤ D) (A : Type (w + 1)) [Category.{w} A] [Preadditive A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J A] :
    (G.sheafPullbackCocontinuous A J K).PreservesZeroMorphisms := by
  unfold sheafPullbackCocontinuous
  exact preservesZeroMorphisms_comp (sheafToPresheaf K A)
    ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op ⋙ presheafToSheaf J A)

end CategoryTheory.Functor
