/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Flat.FiniteFreeFactorization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.81.2
@stack 058E
-/

/- Lemma 10.81.2: an `R`-module `M` is flat if and only if every linear map from a finitely
presented `R`-module to `M` factors through some finite free `R`-module. -/
@[stacks 058E]
#check @Module.Flat.iff_finiteFree_factorization

@[stacks 058E "finite-free factorization owner"]
#check @Module.Flat.exists_factorization_of_finitePresentation

@[stacks 058E "equational flatness criterion"]
#check @Module.Flat.iff_forall_exists_factorization
