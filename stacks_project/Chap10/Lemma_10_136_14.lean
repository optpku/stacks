/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Polynomial.Splitting

@[expose] public section

/-!
# Syntomic Splitting Extension Recall

The reusable owner bundles the finite and free module laws as `RingHom.FiniteFree`;
`RingHom.finiteFree_algebraMap` exposes the equivalent source-facing conjunction.

@stack 03HS
-/

/- Lemma 10.136.14: a monic polynomial splits after a syntomic, finite-free, faithfully flat
extension of its coefficient ring. -/
@[stacks 03HS "syntomic finite-free splitting extension"]
#check @Polynomial.Monic.exists_syntomic_faithfullyFlat_splits_map

@[stacks 03HS "finite-free algebra-map characterization"]
#check @RingHom.finiteFree_algebraMap
