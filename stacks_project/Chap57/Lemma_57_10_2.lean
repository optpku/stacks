module

import ReasLib.CategoryTheory.DerivedCategory.Bounded.Sibling
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe wA vA uA vD uD

namespace CategoryTheory.Functor

/- Lemma 57.10.2: exact triangulated functors `F, F' : DerivedCategory.Bounded A ⥤ D`
that are isomorphic after restriction along the heart inclusion
`i = DerivedCategory.Bounded.singleFunctor A 0`, and such that
`ShiftedHom (F.obj (i.obj X)) (F.obj (i.obj Y)) q` is a `Subsingleton` for all
objects `X, Y` of `A` and all `q < 0`, are siblings. -/
@[stacks 0FZU] #check
  (CategoryTheory.Functor.areSiblings_of_restrictIso_of_negShiftedHom :
    ∀ {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
      {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
      [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
      [_root_.CategoryTheory.IsTriangulated D]
      (F F' : DerivedCategory.Bounded A ⥤ D)
      [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
      (hiso : Nonempty (DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F ≅
          DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F'))
      (hvanish : ∀ (X Y : A) (q : ℤ), q < 0 →
        Subsingleton
          (ShiftedHom (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj X))
            (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj Y)) q)),
      areSiblings F F')

#check
  (CategoryTheory.Functor.negShiftedHom_subsingleton_of_fullyFaithful :
    ∀ {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
      {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
      [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
      [_root_.CategoryTheory.IsTriangulated D]
      (F : DerivedCategory.Bounded A ⥤ D)
      [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful]
      (X Y : A) (q : ℤ) [Fact (q < 0)],
      Subsingleton
        (ShiftedHom (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj X))
          (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj Y)) q))

end CategoryTheory.Functor
