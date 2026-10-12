/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap57.Definition_57_10_1
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe wA vA uA vD uD

/- Definition 57.12.1: for finite-type schemes over a field, the coherent derived
functors are called siblings when they satisfy the sibling relation of Definition
57.10.1; for a regular scheme, the same terminology applies to the corresponding
perfect derived functors under the cited coherent-perfect comparison. -/
@[stacks 0FZZ] #check (CategoryTheory.Functor.areSiblings :
  ∀ {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated], Prop)
