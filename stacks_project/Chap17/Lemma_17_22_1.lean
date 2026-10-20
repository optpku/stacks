/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

/-!
# Lemma 17.22.1

The tensor--internal-Hom currying isomorphism is owned at the level of braided closed monoidal
categories; the ringed-space statement is its canonical specialization.
-/

@[expose] public section

/- Lemma 17.22.1 (01CN): internal Hom out of a tensor product is canonically the iterated
internal Hom. -/
@[stacks 01CN]
#check @CategoryTheory.MonoidalClosed.internalHomTensorIso

/- The reusable owner is a natural isomorphism in the target, with independently named forward
and inverse natural transformations. -/
#check @CategoryTheory.MonoidalClosed.InternalHomTensor.natIso
#check @CategoryTheory.MonoidalClosed.InternalHomTensor.natTrans
#check @CategoryTheory.MonoidalClosed.InternalHomTensor.natTransInv
