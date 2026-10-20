/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.IdealPower.System.IsIso

/-!
# Lemma 15.101.7

@stack 0EGX
-/

@[expose] public section

open CategoryTheory
open IadicFiniteModuleSystem

/- Lemma 15.101.7 (0EGX): a morphism in the quotient category of finite A / I ^ n-module systems
is an isomorphism exactly when one (equivalently every) representative has an eventual uniform
ideal-power bound on its stagewise kernel and cokernel.  The predicate and criterion are owned by
ReasLib; this chapter file is boundary-only.
-/

@[stacks 0EGX "stagewise kernel of a representative"]
#check @IadicFiniteModuleSystem.HomRepresentative.levelKernel
@[stacks 0EGX "stagewise cokernel of a representative"]
#check @IadicFiniteModuleSystem.HomRepresentative.levelCokernel
@[stacks 0EGX "eventual bounded kernel and cokernel for a representative"]
#check @IadicFiniteModuleSystem.HomRepresentative.HasUniformTorsionBound
@[stacks 0EGX "eventual bounded kernel and cokernel in the quotient category"]
#check @IadicFiniteModuleSystem.Category.HasBound
@[stacks 0EGX "isomorphism criterion by eventual kernel-cokernel bounds"]
#check @IadicFiniteModuleSystem.Category.isIso_iff_hasBound
@[stacks 0EGX "representative-level isomorphism criterion"]
#check @IadicFiniteModuleSystem.HomRepresentative.isIso_quotientMap_iff
