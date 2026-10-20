/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.GRing.CompleteLocalPolynomial
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.50.9 (07PU)

@stack 07PU
-/


/- Lemma 15.50.9: the polynomial formal fiber in the specified complete-local-domain situation is
geometrically regular. -/
@[stacks 07PU "Lemma 15.50.9"]
#check @IsCompleteLocalRing.polynomial_formalFiber_isGeometricallyRegular

#check @IsGRing.of_finiteType
