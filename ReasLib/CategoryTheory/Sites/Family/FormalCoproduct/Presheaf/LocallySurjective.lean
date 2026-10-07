module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Covering

/-!
# Locally surjective maps to presheaves of semi-representable families

This leaf converts local surjectivity onto a coproduct of representables into a covering
semi-representable-family morphism through which the presheaf map factors.  Both the ordinary
and fixed-target forms are exposed for reuse by refinement constructions.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [Small.{w} C] [LocallySmall.{w} C]

namespace SemiRepresentableFamily

/-- A locally surjective map onto the presheaf of a semi-representable family factors through
the presheaf map of a covering family morphism. -/
theorem existsCoveringFactorization
    (K : SR(C)) {F : Cᵒᵖ ⥤ Type (max w v)}
    (u : F ⟶ Limits.FormalCoproduct.toPresheaf.obj K)
    [Presheaf.IsLocallySurjective J u] :
    ∃ (L : SR(C)) (φ : L ⟶ K)
      (g : Limits.FormalCoproduct.toPresheaf.obj L ⟶ F),
      SemiRepresentableFamily.covering J φ ∧
        Limits.FormalCoproduct.toPresheaf.map φ = g ≫ u := sorry

namespace OverFamily

/-- A locally surjective map onto the presheaf of a fixed-target semi-representable family
factors through the underlying presheaf map of a covering fixed-target family morphism. -/
theorem existsCoveringFactorization
    {X : C} (K : SR(C, X)) {F : Cᵒᵖ ⥤ Type (max w v)}
    (u : F ⟶ Limits.FormalCoproduct.toPresheaf.obj (forget.obj K))
    [Presheaf.IsLocallySurjective J u] :
    ∃ (L : SR(C, X)) (φ : L ⟶ K)
      (g : Limits.FormalCoproduct.toPresheaf.obj (forget.obj L) ⟶ F),
      SemiRepresentableFamily.OverFamily.covering J φ ∧
        Limits.FormalCoproduct.toPresheaf.map (forget.map φ) = g ≫ u := sorry

end OverFamily

end SemiRepresentableFamily

end CategoryTheory
