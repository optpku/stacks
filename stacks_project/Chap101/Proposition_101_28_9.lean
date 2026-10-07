module

public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Lemma_101_5_1
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# When an algebraic stack is a gerbe

An algebraic stack is a gerbe if and only if its canonical inertia morphism is
flat and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Proposition 101.28.9: let `X` be an algebraic stack. Then `X` is a gerbe if
and only if the canonical inertia morphism `Inertia.forget X : inertia X ⟶ X`
is flat and locally of finite presentation. -/
@[stacks 06QJ]
theorem isGerbe_iff_inertia_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsGerbe X ↔
      Flat (forget.{u + 1, u, u, u + 1} X) ∧
        LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X) := sorry

namespace Inertia

/-- The inertia morphism of a gerbe algebraic stack is flat. -/
instance instFlat_forget {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsGerbe X] : Flat (forget.{u + 1, u, u, u + 1} X) :=
  sorry

/-- The inertia morphism of a gerbe algebraic stack is locally of finite
presentation. -/
instance instLocallyOfFinitePresentation_forget {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsGerbe X] :
    LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X) :=
  sorry

end Inertia

/-- An algebraic stack whose inertia morphism is flat and locally of finite
presentation is a gerbe. -/
instance instIsGerbe_of_inertia_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Flat (forget.{u + 1, u, u, u + 1} X)]
    [LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X)] :
    IsGerbe X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
