/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.TorsionComplete
public import stacks_project.Chap47.Lemma_47_12_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Proposition 47.12.2: for a finitely generated ideal `I`, derived completion
and closed-support local cohomology restrict to quasi-inverse equivalences between
derived objects with `I`-power-torsion cohomology and derived-complete objects. -/
@[stacks 0A6X] #check
  (CategoryTheory.DerivedCategory.TorsionComplete.equivalence :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤
        CategoryTheory.DerivedCategory.IdealPowerTorsion I)
      (hRΓZ : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓZ),
      CategoryTheory.DerivedCategory.IdealPowerTorsion I ≌
        DerivedCategory.DerivedComplete.category I)
