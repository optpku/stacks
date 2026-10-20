/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.Theory
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Filtration.Invertible

@[expose] public section

open CategoryTheory

universe u v w x y

namespace AlgebraicGeometry.ChernClass.CohomologyTheory

/-- A finite family of finite locally free modules acquires invertible-quotient filtrations
of its prescribed ranks after a pullback that is injective on the graded cohomology ring of
a Chern-class theory. -/
theorem existsInjectiveSplittingPullback
    {C : Type u} [Category.{v} C] {toScheme : C ⥤ Scheme.{w}}
    {A : Cᵒᵖ ⥤ RingCat.{x}}
    {Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X))}
    [gradedAlgebra : ∀ X, GradedAlgebra (Agrade X)] (S : CohomologyTheory toScheme A Agrade)
    {ι : Type y} [Finite ι] (X : C) (E : ι → (toScheme.obj X).Modules)
    (r : ι → ℕ) [∀ index, Scheme.Modules.IsFiniteLocallyFreeOfRank (r index) (E index)] :
    ∃ (P : C) (p : P ⟶ X),
      Function.Injective (A.map p.op) ∧
        ∀ index, Scheme.Modules.HasInvertibleQuotientFiltrationOfLength (r index)
          ((Scheme.Modules.pullback (toScheme.map p)).obj (E index)) := sorry

end AlgebraicGeometry.ChernClass.CohomologyTheory
