module

public import Mathlib.CategoryTheory.Sites.Continuous

@[expose] public section

universe u₁ u₂ v₁ v₂ w t

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Forgetting the sheaf condition after continuous pushforward is precomposition
of the underlying presheaf with the opposite functor. -/
theorem sheafPushforwardContinuous_comp_sheafToPresheaf
    (u : C ⥤ D) (A : Type w) [Category.{t} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] :
    u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A =
      sheafToPresheaf K A ⋙ (CategoryTheory.Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op := rfl

end CategoryTheory.Functor
