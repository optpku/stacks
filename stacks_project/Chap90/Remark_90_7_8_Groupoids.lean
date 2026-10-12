/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Cofibered.InGroupoids

/-!
# Categories cofibered in groupoids

The generic constructors and projections are supplied by the shared cofibered-groupoid owner.
-/

@[expose] public section

open CategoryTheory

universe u v w vS

variable {C : Type u} [Category.{v} C]

/- The constructor of a cofibered-groupoid category from its projection functor. -/
#check (CategoryTheory.CofiberedCategoryOver.Groupoids.ofFunctor :
  {S : Type w} → [Category.{vS} S] → (p : S ⥤ C) →
    [Functor.IsFibered.InGroupoids p.op] → CofiberedCategoryOver.Groupoids C)
