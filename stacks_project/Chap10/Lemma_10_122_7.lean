/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.QuasiFinite.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.122.7

@stack 00PN

Quasi-finiteness at a prime is preserved by a surjective quotient of a tensor-product base
change. The statement retains the source's finite-type hypothesis and conclusion.
-/

@[stacks 00PN "base-change direction"]
#check @Algebra.QuasiFiniteAt.baseChange
@[stacks 00PN "descent along surjective stalk maps"]
#check @Algebra.QuasiFiniteAt.of_surjectiveOnStalks

/- Lemma 10.122.7: let `R → S`, `R → R'`, `S → S'`, and `R' → S'` form a commutative
diagram, with `R → S` of finite type and the canonical map `R' ⊗[R] S → S'` surjective. If
`R → S` is quasi-finite at the prime below `q'`, then `R' → S'` is finite type and quasi-finite
at `q'`. -/
@[stacks 00PN]
#check @Algebra.FiniteType.quasiFiniteAt_baseChange_of_surjective
