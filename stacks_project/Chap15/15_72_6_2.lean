/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Differential
import StacksCheckRecall

/-!
# Differential of a homogeneous tensor component

The tensor-total differential is recorded on an actual pure tensor
`Cochain.single g (p + q) ⊗ₜ k`, so all three source terms and their signs are visible in one
typed statement.
-/

@[expose] public section

/-!
# 15.72.6.2

@stack 0FNF
-/

open CochainComplex.HomComplex
open CategoryTheory.CochainComplex.InternalHom.Module.Differential

/- Equation 15.72.6.2: the `M`, `L`, and `K` contributions have coefficients
`1`, `-(-1)^(p+q)`, and `(-1)^(p+q)`. -/
@[stacks 0FNF "three-term tensor-total differential on a homogeneous pure tensor"]
#check @tensorDifferential_single_tmul

#check @Cochain.δ_single
#check @HomologicalComplex.mapBifunctor.d_eq
