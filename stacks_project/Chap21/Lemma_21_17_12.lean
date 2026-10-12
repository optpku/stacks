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
# Lemma 21.17.12

The varying-factor K-flat tensor-invariance theorem is owned by the ringed-site complex API in
ReasLib.  Its canonical instances provide the tensor-totalization and resolution infrastructure.
-/

/- Lemma 21.17.12 (06YT): tensoring an arbitrary complex with a quasi-isomorphism between K-flat
complexes preserves quasi-isomorphisms. -/
@[stacks 06YT]
#check @SheafOfModules.RingedSite.CochainComplex.IsKFlat.quasiIso_tensorHom_right

#check @CochainComplex.IsKFlat.quasiIso_tensorHom_right
