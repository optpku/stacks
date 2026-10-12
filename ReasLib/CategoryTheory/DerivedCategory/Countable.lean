/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory

/-- A countable abelian category has a countable skeleton of its bounded derived category. -/
instance countableCategory_boundedDerived
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [CountableCategory (Skeleton A)] :
    CountableCategory (Skeleton (DerivedCategory.Bounded A)) := sorry

end CategoryTheory
