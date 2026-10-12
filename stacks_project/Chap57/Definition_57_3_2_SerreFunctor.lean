/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.SerreFunctor.Structure

@[expose] public section

open CategoryTheory

universe w v u

#check (CategoryTheory.SerreFunctor :
  (k : Type w) → (T : Type u) → [Field k] → [CategoryTheory.Category.{v} T] →
    [CategoryTheory.Preadditive T] → [CategoryTheory.Linear k T] →
    Type (max (max u v) w))
