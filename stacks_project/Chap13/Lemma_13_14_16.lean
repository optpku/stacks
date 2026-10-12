/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

-- Lemma 13.14.16: comparison natural transformations `R(G ∘ F) ⟶ RG ∘ RF'` and
-- `LG ∘ LF' ⟶ L(G ∘ F)` between the total derived functor of a composite and the composite of
-- total derived functors. Now lives in the shared library, together with the homotopy-category
-- functoriality helpers it depends on.
@[stacks 05T2] #check @CategoryTheory.Functor.RightDerived.Composition.comparison
#check @CategoryTheory.Functor.RightDerived.Composition.comparison_fac
#check @CategoryTheory.Functor.RightDerived.Composition.comparison_fac_app
#check @CategoryTheory.Functor.LeftDerived.Composition.comparison
#check @CategoryTheory.Functor.LeftDerived.Composition.comparison_fac
#check @CategoryTheory.Functor.LeftDerived.Composition.comparison_fac_app

-- The shared root owner is neutral in the localization functors and in the chosen derived models.
#check @CategoryTheory.Functor.RightDerived.Composition.iteratedUnit
#check @CategoryTheory.Functor.RightDerived.Composition.iteratedUnit_app
#check @CategoryTheory.Functor.RightDerived.Composition.comparisonOfModels
#check @CategoryTheory.Functor.RightDerived.Composition.comparisonOfModels_fac_app
#check @CategoryTheory.Functor.LeftDerived.Composition.iteratedCounit
#check @CategoryTheory.Functor.LeftDerived.Composition.iteratedCounit_app
#check @CategoryTheory.Functor.LeftDerived.Composition.comparisonOfModels
#check @CategoryTheory.Functor.LeftDerived.Composition.comparisonOfModels_fac_app

#check @CategoryTheory.Functor.mapHomotopyCategoryCompIso
#check @CategoryTheory.Functor.mapHomotopyCategoryIso
