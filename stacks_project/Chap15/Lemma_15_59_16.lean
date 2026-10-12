/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Factorization

/-!
# Lemma 15.59.16

@stack 0G6M

The reusable commutative-ring factorization statements are owned in the `CochainComplex`
namespace, with the termwise-flat conclusion exposed as a separate refinement.
-/

@[expose] public section

/- Lemma 15.59.16 (1): a map with K-flat source factors up to homotopy through a
quasi-isomorphism from a K-flat complex. -/
@[stacks 0G6M "K-flat factorization"]
#check @CochainComplex.exists_kFlat_factorization_up_to_homotopy

/- Lemma 15.59.16 (2): if the source is termwise flat, the intermediate K-flat complex can be
chosen termwise flat. -/
@[stacks 0G6M "termwise-flat K-flat factorization"]
#check @CochainComplex.exists_termwiseFlat_kFlat_factorization_up_to_homotopy
