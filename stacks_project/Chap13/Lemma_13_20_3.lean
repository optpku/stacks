/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Bounded.DeltaFunctor
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor
import StacksCheckRecall

@[expose] public section

/- Lemma 13.20.3 is the canonical delta-functor structure on the bounded-below
derived localization of cochain complexes, and its degree-zero specialization.
For any exact `RF : D⁺(A) ⥤ D⁺(B)`, postcomposition gives the two source
delta functors. -/

open CategoryTheory
open CategoryTheory.Pretriangulated

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
  [RF.CommShift ℤ] [RF.IsTriangulated]

@[stacks 0159] #check @DerivedCategory.Plus.Qh.compInclusionIso
@[stacks 0159] #check @DerivedCategory.Plus.Delta.connecting

@[stacks 0159] #check
  ((DerivedCategory.Plus.Delta.functor A).postcomposeExactFunctor RF :
    DeltaFunctor (CochainComplex.Plus A) (DerivedCategory.Plus B))

@[stacks 0159] #check
  ((DerivedCategory.Plus.singleFunctor.delta A).postcomposeExactFunctor RF :
    DeltaFunctor A (DerivedCategory.Plus B))

end CategoryTheory
