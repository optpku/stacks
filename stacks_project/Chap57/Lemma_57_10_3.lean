/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Sibling
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe wA vA uA vD uD

namespace CategoryTheory.Functor

/- Lemma 57.10.3 (1): if sibling exact triangulated functors `F` and `F'` have
`F` essentially surjective, then `F'` is essentially surjective. -/
@[stacks 0FZV] #check (CategoryTheory.Functor.essSurj_of_areSiblings :
    ∀ {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
      {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
      [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
      [_root_.CategoryTheory.IsTriangulated D]
      (F F' : DerivedCategory.Bounded A ⥤ D)
      [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated],
      areSiblings F F' → ∀ [F.EssSurj], F'.EssSurj)

/- Lemma 57.10.3 (2): if sibling exact triangulated functors `F` and `F'` have
`F` fully faithful, then `F'` is fully faithful. -/
@[stacks 0FZV] #check (CategoryTheory.Functor.fullyFaithful_of_areSiblings :
    ∀ {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
      {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
      [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
      [_root_.CategoryTheory.IsTriangulated D]
      (F F' : DerivedCategory.Bounded A ⥤ D)
      [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated],
      areSiblings F F' → Nonempty F.FullyFaithful → Nonempty F'.FullyFaithful)

end CategoryTheory.Functor
