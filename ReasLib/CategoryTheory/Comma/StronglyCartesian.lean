module

public import ReasLib.CategoryTheory.Comma.Pullback
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Comma

variable {B : Type u₁} {C : Type u₂} [Category.{v₁} B] [Category.{v₂} C]
variable [Limits.HasPullbacks C]

/-- A comma morphism is strongly cartesian for the second projection if and only if
its canonical map to the pullback along its base morphism is an isomorphism. -/
theorem isStronglyCartesian_iff_isIso_pullback (G : B ⥤ C)
    (source target : Comma (𝟭 C) G) (φ : source ⟶ target) :
    (Comma.snd (𝟭 C) G).IsStronglyCartesian φ.right φ ↔
      IsIso ((Comma.homEquivSigmaPullback G source target φ).2.left) := sorry

end CategoryTheory.Comma
