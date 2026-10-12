/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ZeroFunctor
public import ReasLib.CategoryTheory.Adjunction.Abelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Remark 12.29.4 (1) [03B9]: the source's zero-object detection condition is the canonical
kernel inclusion `v.kernel ≤ IsZero`. -/
@[stacks 03B9 "(1)"]
#check @Adjunction.kernel_le_isZero_iff_faithful

/- Remark 12.29.4 (2) [03B9]: the two positive zero-functor properties and the two failure
criteria are category-general; the regular `ZMod 2`-module supplies the concrete nonzero witness.
-/
@[stacks 03B9 "(2)"]
#check (Functor.zero_isLeftAdjoint (C := ModuleCat.{0} (ZMod 2)))

@[stacks 03B9 "(2)"]
#check (Functor.zero_preservesMonomorphisms (C := ModuleCat.{0} (ZMod 2)))

@[stacks 03B9 "(2)"]
#check ModuleCat.ZeroFunctor.zModTwo_regular_not_isZero

@[stacks 03B9 "(2)"]
#check @Functor.zero_not_kernel_le_isZero_of_not_isZero

@[stacks 03B9 "(2)"]
#check @Functor.zero_not_faithful_of_not_isZero
