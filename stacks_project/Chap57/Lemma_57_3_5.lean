module

public import stacks_project.Chap57.Definition_57_3_2_SerreFunctor
public import ReasLib.CategoryTheory.SerreFunctor.Uniqueness
public import ReasLib.CategoryTheory.SerreFunctor.Triangulated

import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.SerreFunctor

/- Lemma 57.3.5 (1) -/
@[stacks 0FY6] #check (CategoryTheory.SerreFunctor.uniqueIso :
  ∀ {T : Type u} [Category.{v} T] [Preadditive T]
    {k : Type w} [Field k] [Linear k T]
    [Limits.HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T],
    (∀ X Y : T, FiniteDimensional k (X ⟶ Y)) →
    ∀ (S S' : SerreFunctor k T),
      ∃! e : S.toEquivalence.functor ≅ S'.toEquivalence.functor,
        IsCompatible S S' e)

/- Lemma 57.3.5 (2) -/
@[stacks 0FY6] #check (CategoryTheory.SerreFunctor.hasTriangulatedStructure :
  ∀ {T : Type u} [Category.{v} T] [Preadditive T]
    {k : Type w} [Field k] [Linear k T]
    [Limits.HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T],
    (∀ X Y : T, FiniteDimensional k (X ⟶ Y)) →
    ∀ (S : SerreFunctor k T),
      Functor.HasTriangulatedStructure S.toEquivalence.functor)

end CategoryTheory.SerreFunctor

end
