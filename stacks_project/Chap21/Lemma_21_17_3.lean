/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.QuasiIso
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.17.3

The fixed-right K-flat tensor-invariance statement is owned by the ringed-site complex API in
ReasLib; no Chapter 15 implementation is imported here.
-/

/- Lemma 21.17.3 (06YP): tensoring a quasi-isomorphism on the left with a fixed K-flat complex
of module sheaves preserves quasi-isomorphisms. -/
@[stacks 06YP]
#check @SheafOfModules.RingedSite.CochainComplex.IsKFlat.tensorHom_right_quasiIso

#check @CochainComplex.IsKFlat.quasiIso_tensorHom_left
