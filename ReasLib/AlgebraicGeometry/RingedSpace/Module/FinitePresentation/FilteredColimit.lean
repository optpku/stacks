module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.FilteredColimit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.CategoryTheory.Sites.FilteredColimits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely presented module sheaves on suitable ringed spaces

This file turns the geometric finite-cover hypothesis on a ringed space into the canonical
category-theoretic interface: a finitely presented module sheaf is a finitely presentable object.
Downstream filtered-colimit arguments can therefore use `IsFinitelyPresentable` directly.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.IsFinitePresentation

/-- Lemma 17.22.8 (01BS), reusable owner: on a ringed space whose top open has cofinal finite
cover refinements with quasi-compact pairwise overlaps, a finitely presented module sheaf is a
finitely presentable object of the module-sheaf category. -/
@[stacks 01BS, instance]
theorem isFinitelyPresentable
    {X : RingedSpace.{u}} (F : X.Modules) [F.IsFinitePresentation]
    [(Opens.grothendieckTopology X).HasCofinalRefinement (⊤ : Opens X)] :
    IsFinitelyPresentable.{u} F := sorry

end SheafOfModules.IsFinitePresentation
