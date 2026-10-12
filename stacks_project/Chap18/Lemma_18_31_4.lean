/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.InternalHom
import StacksCheckRecall

/-!
# Lemma 18.31.4

The reusable theorem is the flat specialization of the general exact-pullback criterion in the
pullback/internal-Hom namespace.
-/

@[expose] public section

/- Lemma 18.31.4 (0GN2): flat pullback commutes with internal Hom from a finitely presented
module. -/
@[stacks 0GN2]
#check @RingedSite.Hom.PullbackInternalHom.isIso_of_isFlat
