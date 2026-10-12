/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.QuasiIso

@[expose] public section

/-!
# Lemma 15.96.3

@stack 0F7Q
-/

/-! # The Berthelot-Ogus eta operator preserves quasi-isomorphisms -/

/- Lemma 15.96.3, tag `0F7Q`: a quasi-isomorphism between integer-indexed complexes of
termwise `f`-torsion-free modules induces a quasi-isomorphism after applying `η_f`. -/
@[stacks 0F7Q "Berthelot-Ogus eta preserves quasi-isomorphisms"]
#check @CochainComplex.BerthelotOgus.Int.functor_map_quasiIso
