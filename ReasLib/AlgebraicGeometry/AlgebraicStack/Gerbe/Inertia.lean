/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Gerbes and inertia

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

/-- An algebraic stack is a gerbe if and only if its canonical inertia morphism
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
  ((isGerbe_iff_inertia_flat_locallyOfFinitePresentation X).mp inferInstance).1

/-- The inertia morphism of a gerbe algebraic stack is locally of finite
presentation. -/
instance instLocallyOfFinitePresentation_forget {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsGerbe X] :
    LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X) :=
  ((isGerbe_iff_inertia_flat_locallyOfFinitePresentation X).mp inferInstance).2

end Inertia

/-- An algebraic stack whose inertia morphism is flat and locally of finite
presentation is a gerbe. -/
instance instIsGerbe_of_inertia_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Flat (forget.{u + 1, u, u, u + 1} X)]
    [LocallyOfFinitePresentation (forget.{u + 1, u, u, u + 1} X)] :
    IsGerbe X :=
  (isGerbe_iff_inertia_flat_locallyOfFinitePresentation X).mpr
    ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.AlgebraicStack
