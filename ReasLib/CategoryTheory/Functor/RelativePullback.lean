module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Relative pullbacks along a functor

A relative pullback represents compatible pairs of morphisms tested on objects
and morphisms of the source category.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The maps `p` and `q` represent compatible pairs of maps into `U` and `W`,
with compatibility tested after applying `u` to the map into `U`. -/
def IsRelativePullback (u : C ⥤ D) {Z U : C} {W V : D}
    (p : Z ⟶ U) (q : u.obj Z ⟶ W) (g : u.obj U ⟶ V) (f : W ⟶ V) : Prop :=
  u.map p ≫ g = q ≫ f ∧
    ∀ (T : C) (a : T ⟶ U) (b : u.obj T ⟶ W), u.map a ≫ g = b ≫ f →
      ∃! l : T ⟶ Z, l ≫ p = a ∧ u.map l ≫ q = b

/-- Relative pullbacks along the identity functor are ordinary pullback squares. -/
theorem isRelativePullback_id_iff {Z U W V : C}
    (p : Z ⟶ U) (q : Z ⟶ W) (g : U ⟶ V) (f : W ⟶ V) :
    (𝟭 C).IsRelativePullback p q g f ↔ IsPullback p q g f := sorry

end CategoryTheory.Functor
