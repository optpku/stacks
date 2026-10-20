/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

/-!
# Lemma 18.27.6 compatibility facade

The reusable braided closed monoidal category API is owned by
`ReasLib.CategoryTheory.Monoidal.Closed.Braided`. This module preserves the
historical Chapter 18 import path and source traceability.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

/- Lemma 18.27.6 (1) (03EO): the presheaf statement is the generic tensor/internal-Hom
isomorphism in a braided closed monoidal category. -/
@[stacks 03EO "(1)"]
#check @MonoidalClosed.internalHomTensorIso

/- Its Hom-set specialization is generic source-order currying. -/
#check MonoidalClosed.braidedHomEquiv

/- Lemma 18.27.6 (2) (03EO): the sheaf statement has the same generic owner. -/
@[stacks 03EO "(2)"]
#check @MonoidalClosed.internalHomTensorIso

/- Functoriality in all three entries is exposed separately for downstream rewriting. -/
#check @MonoidalClosed.internalHomTensorIso_natural_left
#check @MonoidalClosed.internalHomTensorIso_natural_middle
#check @MonoidalClosed.internalHomTensorIso_natural_right
