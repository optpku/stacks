/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Grothendieck Abelian Functor Categories

This leaf records the Grothendieck-abelian structure on a small functor category. It is the
category-level owner for applications to sequential inverse systems, presheaves, and other
diagram categories.
-/

@[expose] public section

universe w vJ uJ vA uA

namespace CategoryTheory

/-- A functor category indexed by a category small relative to `w`, and valued in a
Grothendieck abelian category relative to `w`, is Grothendieck abelian. -/
instance functorCategory_isGrothendieckAbelian
    {J : Type uJ} [Category.{vJ} J] [Small.{w} J] [LocallySmall.{w} J]
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{w} A] :
    IsGrothendieckAbelian.{w} (J ⥤ A) := sorry

end CategoryTheory
