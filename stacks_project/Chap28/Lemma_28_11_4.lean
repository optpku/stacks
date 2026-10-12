/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Catenary

open AlgebraicGeometry
open TopologicalSpace

universe u

variable (S : Scheme.{u})

/- Lemma 28.11.4: a scheme is catenary if and only if every stalk ring is catenary. -/
@[stacks 02J0] #check
  (AlgebraicGeometry.Scheme.catenarySpace_iff_forall_isCatenaryRing_stalk S :
    CatenarySpace S ↔ ∀ x : S, IsCatenaryRing (S.presheaf.stalk x))
