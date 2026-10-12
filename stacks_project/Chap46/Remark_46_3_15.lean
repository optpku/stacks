/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Projective

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

/- Remark 46.3.15 -/
@[stacks 06V7] #check (ModuleValuedFunctor.TensorLinearlyAdequate.projective :
  {A : CommRingCat.{u}} → (L : TensorAdeq A) →
    TensorLinearlyAdequate L.obj → CategoryTheory.Projective L)

#check (ModuleValuedFunctor.TensorLinearlyAdequate.shortExact_isSplitEpi :
  {A : CommRingCat.{u}} → {F G L : TensorAdeq A} →
    (i : F.obj ⟶ G.obj) → (p : G.obj ⟶ L.obj) →
    (h_zero : i ≫ p =
      (@HasZeroMorphisms.zero (ModuleValuedFunctor.bundled A) _
        (ModuleValuedFunctor.bundledHasZeroMorphisms A) F.obj L.obj).zero) →
    (@ShortComplex.ShortExact (ModuleValuedFunctor.bundled A) _
      (ModuleValuedFunctor.bundledHasZeroMorphisms A)
      (@ShortComplex.mk (ModuleValuedFunctor.bundled A) _
        (ModuleValuedFunctor.bundledHasZeroMorphisms A) _ _ _ i p h_zero)) →
    TensorLinearlyAdequate L.obj → IsSplitEpi p)

end ModuleValuedFunctor
