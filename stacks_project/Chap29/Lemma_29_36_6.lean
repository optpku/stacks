/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.36.6: an étale morphism is locally quasi-finite. -/
@[stacks 03WS] #check
  (AlgebraicGeometry.Etale.locallyQuasiFinite :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.Etale f → AlgebraicGeometry.LocallyQuasiFinite f)
