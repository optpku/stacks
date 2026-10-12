/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.QuasiIso
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.59.12: tensor invariance between K-flat complexes

@stack 064L
-/

/- Lemma 15.59.12, tag `064L`: tensoring an arbitrary complex with a quasi-isomorphism between
K-flat complexes preserves quasi-isomorphisms.  The source-facing owner specializes the generic
categorical theorem to `ModuleCat`, where K-flat resolutions are available. -/
@[stacks 064L "quasi-isomorphisms between K-flat complexes"]
#check @ModuleCat.KFlat.quasiIso_tensorHom_right

/- The generic categorical core before discharging the K-flat resolution hypothesis. -/
#check @CochainComplex.IsKFlat.quasiIso_tensorHom_right
