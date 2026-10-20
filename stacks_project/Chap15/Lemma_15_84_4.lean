/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.FlatModel.Bounded
import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Basic
import StacksCheckRecall

/-!
# Lemma 15.84.4: relative perfect objects and bounded flat models

@stack 0DHV
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape
open scoped CategoryTheory

universe u

/- Lemma 15.84.4 (Stacks `0DHV`): relative perfectness is equivalent to admitting the
source's bounded `Compᵇ` model with relatively flat, finitely presented terms. -/
@[stacks 0DHV "bounded relative-flat representative criterion"]
#check fun (R : Type u) {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A)) =>
  (CategoryTheory.DerivedCategory.IsPerfectOver.iff_exists_bounded_flat_finitePresentation_representative
    R K : K.IsPerfectOver R ↔
      ∃ P : Compᵇ((ModuleCat A)),
        CochainComplex.IsTermwiseFlat
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj
            P.obj) ∧
          (∀ i : ℤ, Module.FinitePresentation A (P.obj.X i)) ∧
          IsIsomorphic K (DerivedCategory.Q.obj P.obj))

/- The reusable cochain-complex criterion underlying the bounded source view. -/
#check @CategoryTheory.DerivedCategory.IsPerfectOver.iff_exists_flat_finitePresentation_model
