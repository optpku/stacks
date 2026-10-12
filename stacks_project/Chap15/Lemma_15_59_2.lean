/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.QuasiIso

/-!
# Lemma 15.59.2

@stack 06Y0

The reusable theorem is `CochainComplex.IsKFlat.quasiIso_tensorHom_left`.
It directly expresses that fixed-right tensoring by a K-flat complex preserves
quasi-isomorphisms.
-/

@[expose] public section

/- Lemma 15.59.2 (06Y0): fixed-right tensoring by a K-flat complex preserves
quasi-isomorphisms. -/
@[stacks 06Y0 "fixed K-flat tensor factor preserves quasi-isomorphisms"]
#check @CochainComplex.IsKFlat.quasiIso_tensorHom_left
