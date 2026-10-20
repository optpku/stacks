/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.Equalizer.Finite
import StacksCheckRecall

/-!
# The Noetherian equal-endpoint coordinate ring

@stack 00JG

The finite normalization, conductor decomposition, finite-type structure, and Noetherian
instance are reusable polynomial-algebra facts owned by `Polynomial.EqualEndpoint`.
-/

@[expose] public section

@[stacks 00JG "equal-endpoint subalgebra"]
#check @Polynomial.equalEndpoint

@[stacks 00JG "conductor decomposition"]
#check @Polynomial.EqualEndpoint.exists_eq_C_add_conductor_mul

@[stacks 00JG "finite normalization"]
#check @Polynomial.EqualEndpoint.polynomialModuleFinite

@[stacks 00JG "finite-type equal-endpoint algebra"]
#check @Polynomial.EqualEndpoint.finiteType

@[stacks 00JG "Noetherian equal-endpoint ring"]
#check @Polynomial.EqualEndpoint.isNoetherianRing
