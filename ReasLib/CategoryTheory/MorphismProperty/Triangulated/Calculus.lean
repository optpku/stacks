module

public import ReasLib.CategoryTheory.MorphismProperty.Triangulated.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Fraction Calculi from Triangulation Compatibility

This leaf converts the cancellation clauses used in Verdier localization into
mathlib's left and right calculus-of-fractions owners.
-/

open CategoryTheory Limits Pretriangulated

universe v u

namespace CategoryTheory.MorphismProperty.Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A compatible square on the second and third vertices of distinguished triangles extends to
the first vertex while retaining membership in the morphism property. -/
theorem complete₁
    (S : MorphismProperty D) [S.IsCompatibleWithTriangulation]
    (T₁ T₂ : Triangle D) (hT₁ : T₁ ∈ distTriang D) (hT₂ : T₂ ∈ distTriang D)
    (b : T₁.obj₂ ⟶ T₂.obj₂) (c : T₁.obj₃ ⟶ T₂.obj₃)
    (hb : S b) (hc : S c) (comm : T₁.mor₂ ≫ c = b ≫ T₂.mor₂) :
    ∃ a : T₁.obj₁ ⟶ T₂.obj₁, S a ∧
      T₁.mor₁ ≫ b = a ≫ T₂.mor₁ ∧
        T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := sorry

/-- Stacks 05R3: left cancellation together with triangulation compatibility supplies a left
calculus of fractions. -/
@[stacks 05R3]
theorem hasLeftCalculus
    (S : MorphismProperty D) [S.IsMultiplicative] [S.IsCompatibleWithTriangulation]
    (h_cancel :
      ∀ ⦃X' X Y : D⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X),
        S s → s ≫ f₁ = s ≫ f₂ →
          ∃ (Y' : D) (t : Y ⟶ Y'), S t ∧ f₁ ≫ t = f₂ ≫ t) :
    S.HasLeftCalculusOfFractions := sorry

/-- Stacks 05R3: right cancellation together with triangulation compatibility supplies a right
calculus of fractions. -/
@[stacks 05R3]
theorem hasRightCalculus
    (S : MorphismProperty D) [S.IsMultiplicative] [S.IsCompatibleWithTriangulation]
    (h_cancel :
      ∀ ⦃X Y Y' : D⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y'),
        S s → f₁ ≫ s = f₂ ≫ s →
          ∃ (X' : D) (t : X' ⟶ X), S t ∧ t ≫ f₁ = t ≫ f₂) :
    S.HasRightCalculusOfFractions := sorry

end CategoryTheory.MorphismProperty.Triangulated
