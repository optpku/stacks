/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Finiteness.Projective.FlatLocal

@[expose] public section

/-!
# Finite Projectivity and Flat Local Maps Recall

The reusable owner is `Module.FiniteProjective`; the source theorem is its
flat-local scalar-extension criterion.

@stack 00O1
-/

/- Lemma 10.78.6, tag 00O1: finite projectivity is detected after a flat local
homomorphism of local rings. -/
@[stacks 00O1 "finite projective modules and flat local homomorphisms"]
#check @Module.FiniteProjective.iff_tensorProduct_of_flat_localHom
