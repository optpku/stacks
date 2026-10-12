/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import stacks_project.Chap46.Lemma_46_3_12
public import stacks_project.Chap46.Lemma_46_3_14
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Extension
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 46.3.16 -/
@[stacks 06V8] #check
  (ModuleValuedFunctor.TensorAdequate.isClosedUnderExtensions :
    ∀ (A : CommRingCat.{u}),
      @ObjectProperty.IsClosedUnderExtensions
        (ModuleValuedFunctor.bundled.{u, u} A) _
        (ModuleValuedFunctor.TensorAdequate (A := A))
        (ModuleValuedFunctor.bundledHasZeroMorphisms A))
