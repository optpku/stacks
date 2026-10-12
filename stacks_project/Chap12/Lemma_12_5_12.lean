/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}

section Pullback

variable [HasKernel f] [HasKernel k] (sq : IsPullback g f k h)

/- Lemma 12.5.12 (1): applying the canonical kernel comparison theorem to the flipped
cartesian square gives the induced isomorphism `kernel f ⟶ kernel k`. -/
@[stacks 08N3] #check
  (isIso_kernel_map_of_isPullback sq.flip :
    IsIso (kernel.map f k g h sq.w.symm))

end Pullback

section Pushout

variable [HasCokernel f] [HasCokernel k] (sq : IsPushout g f k h)

/- Lemma 12.5.12 (2): applying the canonical cokernel comparison theorem to the flipped
cocartesian square gives the induced isomorphism `cokernel f ⟶ cokernel k`. -/
#check
  (isIso_cokernel_map_of_isPushout sq.flip :
    IsIso (cokernel.map f k g h sq.w.symm))

end Pushout

end CategoryTheory.Limits
