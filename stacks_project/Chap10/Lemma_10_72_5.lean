/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.Ext
import StacksCheckRecall

/-!
# Lemma 10.72.5

@stack 00LW
-/

@[expose] public section

/- Lemma 10.72.5: for a nonzero finite module `M` over a Noetherian local
ring `R`, `moduleDepth R M` is the least `i` for which
`Ext^i_R(ResidueField R, M)` is nonzero. -/
@[stacks 00LW]
#check @Module.ResidueFieldExt.moduleDepth_eq_firstNonzeroIndex

/- The reusable owner exposes the residue-field Ext group and its nonvanishing
predicate independently of Noetherian and finite-generation hypotheses. -/
#check @Module.ResidueFieldExt
#check @Module.ResidueFieldExt.Nonzero

/- The first nonvanishing degree is concrete `sInf` data, with a specification,
minimality, and a complete vanishing profile for downstream use. -/
#check @Module.ResidueFieldExt.firstNonzeroIndex
#check @Module.ResidueFieldExt.firstNonzeroIndex_spec
#check @Module.ResidueFieldExt.firstNonzeroIndex_le
#check @Module.ResidueFieldExt.firstNonzeroIndex_eq_iff
#check @Module.ResidueFieldExt.not_nonzero_of_lt_firstNonzeroIndex
#check @Module.ResidueFieldExt.profile_of_moduleDepth_eq
