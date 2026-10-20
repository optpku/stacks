/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.BaseChange

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

/- Compatibility bridge for the presentation-defined upper-shriek base-change comparison. -/
#check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.baseChangeComparison :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A))
      (R' : Type u) [CommRing R'] [Algebra R R']
      (hTor : CategoryTheory.ModuleCat.Tor.IsIndependent
        (ModuleCat.of R A) (ModuleCat.of R R')),
      p.functor ⋙
          CategoryTheory.ModuleCat.derivedExtensionOfScalars
            (algebraMap A (A ⊗[R] R')) ⟶
        CategoryTheory.ModuleCat.derivedExtensionOfScalars (algebraMap R R') ⋙
          (p.baseChange R').functor)
