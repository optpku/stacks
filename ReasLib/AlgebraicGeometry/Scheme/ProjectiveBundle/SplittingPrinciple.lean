module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Filtration.Invertible

@[expose] public section

open CategoryTheory

universe u v w x y

namespace AlgebraicGeometry

/-- For a finite family of finite locally free modules, iterated projective-bundle pullback
gives one injective pullback on which every module has an invertible-quotient filtration of
its prescribed rank. -/
theorem exists_injective_splitting_pullback
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x})
    (projectiveBundle :
      ∀ (Y : C) (E : (toScheme.obj Y).Modules) (r : ℕ)
        [Scheme.Modules.IsFiniteLocallyFreeOfRank (r + 1) E],
        Σ (Q : C) (q : Q ⟶ Y),
          Scheme.ProjectiveBundle.Representation (toScheme.map q) E)
    (projectiveBundlePullback_injective :
      ∀ {Y Q : C} (q : Q ⟶ Y) (E : (toScheme.obj Y).Modules) (n : ℕ)
        [Scheme.Modules.IsFiniteLocallyFreeOfRank (n + 1) E],
        Scheme.ProjectiveBundle.Representation (toScheme.map q) E →
          Function.Injective (A.map q.op))
    {ι : Type y} [Finite ι] (X : C) (E : ι → (toScheme.obj X).Modules)
    (r : ι → ℕ) [∀ i, Scheme.Modules.IsFiniteLocallyFreeOfRank (r i) (E i)] :
    ∃ (P : C) (p : P ⟶ X),
      Function.Injective (A.map p.op) ∧
        ∀ i, Scheme.Modules.HasInvertibleQuotientFiltrationOfLength (r i)
          ((Scheme.Modules.pullback (toScheme.map p)).obj (E i)) := sorry

end AlgebraicGeometry
