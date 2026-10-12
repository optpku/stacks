/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import stacks_project.Chap46.Lemma_46_3_5
public import stacks_project.Chap46.Lemma_46_3_6_TensorExtension
public import stacks_project.Chap46.Lemma_46_3_7
public import stacks_project.Chap46.Lemma_46_3_13
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Extension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 46.3.14 -/
@[stacks 06V6] #check (ModuleValuedFunctor.TensorAdequate.of_shortExact_tensorExtension :
    ∀ {A : CommRingCat.{u}} {M : ModuleCat.{u} A}
      {G L : ModuleValuedFunctor.bundled.{u, u} A}
      (i : (ModuleValuedFunctor.tensorExtensionFunctor A).obj M ⟶ G)
      (p : G ⟶ L)
      (h_zero : i ≫ p =
        (@HasZeroMorphisms.zero (ModuleValuedFunctor.bundled.{u, u} A)
          _ (ModuleValuedFunctor.bundledHasZeroMorphisms A)
          ((ModuleValuedFunctor.tensorExtensionFunctor A).obj M) L).zero)
      (h_short :
        @ShortComplex.ShortExact (ModuleValuedFunctor.bundled.{u, u} A) _
          (ModuleValuedFunctor.bundledHasZeroMorphisms A)
          (@ShortComplex.mk (ModuleValuedFunctor.bundled.{u, u} A) _
            (ModuleValuedFunctor.bundledHasZeroMorphisms A) _ _ _ i p h_zero))
      (hL : ModuleValuedFunctor.TensorLinearlyAdequate L),
      ModuleValuedFunctor.TensorAdequate G)
