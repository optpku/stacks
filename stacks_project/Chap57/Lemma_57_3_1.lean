module

public import ReasLib.CategoryTheory.SerreFunctor.Representability

import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.SerreFunctor

/- Lemma 57.3.1 -/
@[stacks 0FY4] #check
  (CategoryTheory.SerreFunctor.exists_iff_representable :
    ∀ {T : Type u} [Category.{v} T] [Preadditive T]
      {k : Type w} [Field k] [Linear k T]
      [Limits.HasZeroObject T] [HasShift T ℤ]
      [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T],
      (∀ X Y : T, FiniteDimensional k (X ⟶ Y)) →
      ((∃ S : T ≌ T, S.functor.Linear k ∧
          ∃ c : ∀ X Y : T,
            (X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ S.functor.obj X),
            (∀ ⦃X X' Y : T⦄ (f : X' ⟶ X) (g : X ⟶ Y)
                (h : Y ⟶ S.functor.obj X'),
              c X' Y (f ≫ g) h = c X Y g (h ≫ S.functor.map f)) ∧
            (∀ ⦃X Y Y' : T⦄ (g : X ⟶ Y) (f : Y ⟶ Y')
                (h : Y' ⟶ S.functor.obj X),
              c X Y' (g ≫ f) h = c X Y g (f ≫ h))) ↔
        ∀ X : T,
          (homDualRight k X).IsRepresentable ∧ (homDualLeft k X).IsCorepresentable))

end CategoryTheory.SerreFunctor

end
