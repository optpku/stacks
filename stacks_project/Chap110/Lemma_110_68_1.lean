module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedBaseChange

/-!
# Derived base change need not lift through D(A ⊗[R] R')
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

/- Lemma 110.68.1: derived base change on modules need not lift to a triangulated
functor `D(A) ⥤ D(A ⊗[R] R')` after restriction to `D(R')`. -/
@[stacks 08J3] #check (CategoryTheory.ModuleCat.DerivedBaseChange.exists_not_exists_functor :
    ∃ (R R' A : Type u) (_ : CommRing R) (_ : CommRing R') (_ : CommRing A)
      (_ : Algebra R R') (_ : Algebra R A),
      ¬ ∃ (T : DerivedCategory (ModuleCat.{u, u} A) ⥤
            DerivedCategory (ModuleCat.{u, u} (A ⊗[R] R'))),
          CategoryTheory.ModuleCat.DerivedBaseChange.LiftsOnModules T)
