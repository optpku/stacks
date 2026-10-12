/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.ActionIsomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

/- Lemma 39.14.2: the action morphism of a quasi-coherent module on a groupoid scheme
is an isomorphism. -/
@[stacks 077Q] #check (AlgebraicGeometry.GroupoidScheme.QCoh.action_isIso :
  ∀ {S : Scheme.{u}} {G : GroupoidScheme S} (A : G.QCoh), IsIso A.action)

end AlgebraicGeometry.GroupoidScheme.QCoh
