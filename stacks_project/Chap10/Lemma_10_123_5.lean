/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Conductor.Polynomial
import Mathlib.RingTheory.ZariskisMainTheorem
import StacksCheckRecall

/-!
# Leading Coefficients and Conductors

@stack 00PX
-/

@[expose] public section

@[stacks 00PX "ring-hom form"]
#check @RingHom.exists_leadingCoeff_pow_mul_mem_conductor

@[stacks 00PX "canonical algebra-hom owner"]
#check @exists_leadingCoeff_pow_smul_mem_conductor
