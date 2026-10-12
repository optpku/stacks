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

/- Proposition 57.10.6: sibling exact triangulated functors are isomorphic when the
source functor is fully faithful and the abelian source category has enough negative objects. -/
@[stacks 0FZW] #check (CategoryTheory.Functor.isomorphic_of_areSiblings :
  ∀ {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (hneg : HasEnoughNegativeObjects A)
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    [F.Full] [F.Faithful] (hsibling : Functor.areSiblings F F'),
    Nonempty (F ≅ F'))
