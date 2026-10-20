module

public import ReasLib.CategoryTheory.SerreFunctor.HomDual
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.SerreFunctor

variable {T : Type u} [Category.{v} T] [Preadditive T]

/-- In a `k`-linear triangulated category with finite-dimensional Hom spaces, a
`k`-linear autoequivalence with bifunctorial Hom-duality pairings exists exactly
when the dualized outgoing Hom functors are representable and the dualized
incoming Hom functors are corepresentable. -/
theorem exists_iff_representable
    {k : Type w} [Field k] [Linear k T]
    [Limits.HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
    (hfinite : ∀ X Y : T, FiniteDimensional k (X ⟶ Y)) :
    (∃ S : T ≌ T, S.functor.Linear k ∧
      ∃ c : ∀ X Y : T,
          (X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ S.functor.obj X),
        (∀ ⦃X X' Y : T⦄ (f : X' ⟶ X) (g : X ⟶ Y)
            (h : Y ⟶ S.functor.obj X'),
          c X' Y (f ≫ g) h = c X Y g (h ≫ S.functor.map f)) ∧
        (∀ ⦃X Y Y' : T⦄ (g : X ⟶ Y) (f : Y ⟶ Y')
            (h : Y' ⟶ S.functor.obj X),
          c X Y' (g ≫ f) h = c X Y g (f ≫ h))) ↔
      ∀ X : T,
        (homDualRight k X).IsRepresentable ∧ (homDualLeft k X).IsCorepresentable := sorry

end CategoryTheory.SerreFunctor

end
