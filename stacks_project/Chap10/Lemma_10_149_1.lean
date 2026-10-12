/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.FirstOrder.SelfPresentation
public import ReasLib.RingTheory.Extension.SectionQuotient
import StacksCheckRecall

/-!
# Existence of Universal First-Order Thickenings

The canonical self-presentation construction and its proof infrastructure are
owned by `Algebra.Extension.FirstOrder.SelfPresentation`.

@stack 04EB
-/

@[expose] public section

@[stacks 04EB "self-presentation section quotient"]
#check @Algebra.Extension.SectionQuotient.extension

@[stacks 04EB "self-presentation section quotient map"]
#check @Algebra.Extension.SectionQuotient.extension_toAlgHom

@[stacks 04EB "self-presentation section quotient section"]
#check @Algebra.Extension.SectionQuotient.extension_σ

@[stacks 04EB "square-zero section quotient"]
#check @Algebra.Extension.SectionQuotient.extension_square_zero

@[stacks 04EB "existence of a universal first-order thickening"]
#check @Algebra.Extension.FirstOrder.existsUniversal
