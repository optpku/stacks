/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Map.Flat
import StacksCheckRecall

@[expose] public section

/-! @stack 0BBY -/

/-
Lemma 10.39.2 (Stacks tag `0BBY`) is owned by
`ReasLib.RingTheory.Ideal.Map.Flat`.  The reusable statements retain the exact
source assumptions: commutative rings, additive commutative-group modules, and
`Module.Flat`; the algebra form is the specialization for a flat algebra map.

The source proof strategy is unchanged: compute the kernel of the product of
the two quotient-tensor maps using flatness, then identify the resulting
submodule with the ideal multiple of `⊤`.  The bundled `Ideal.mapInfTopHom`
is the canonical finite-infimum API used by downstream files.
-/

@[stacks 0BBY "flat module ideal intersection"]
#check @Ideal.smul_top_inf_smul_top_eq_inf_smul_top_of_flat

@[stacks 0BBY "flat algebra ideal intersection"]
#check @Ideal.map_inf_of_flat

@[stacks 0BBY "flat ideal extension InfTopHom"]
#check @Ideal.mapInfTopHom

#check @Ideal.mapInfTopHom_apply
