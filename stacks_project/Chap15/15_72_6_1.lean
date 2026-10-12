/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Differential
import StacksCheckRecall

/-!
# Differential of an iterated Hom component

The exact three-term formula is owned by the module Hom-complex differential API.  The generic
outer formula separates target postcomposition from the two parts of the inner differential.
-/

@[expose] public section

/-!
# 15.72.6.1

@stack 0FNE
-/

open CochainComplex.HomComplex
open CategoryTheory.CochainComplex.InternalHom.Module.Differential

/- Equation 15.72.6.1: the `M`, `L`, and `K` contributions have coefficients
`1`, `-(-1)^n`, and `(-1)^(p+1)`. -/
@[stacks 0FNE "three-term differential of an iterated Hom component"]
#check @betaDifferential_apply

#check @outerDifferential_apply
#check @δ_eq_post_add_pre
