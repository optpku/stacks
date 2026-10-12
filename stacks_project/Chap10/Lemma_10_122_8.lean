/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.QuasiFinite.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.122.8

Composition of quasi-finite ring maps is the canonical Mathlib
`RingHom.QuasiFinite.comp` operation.

@stack 00PO
-/

/- Lemma 10.122.8: a composition of quasi-finite ring maps is quasi-finite. -/
@[stacks 00PO]
#check @Algebra.FiniteType.QuasiFinite.comp

@[stacks 00PO "ring-hom quasi-finite composition"]
#check @RingHom.QuasiFinite.comp
