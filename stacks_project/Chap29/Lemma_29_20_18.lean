/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.20.18: local quasi-finiteness descends through a surjective factor under the stated
local finite-type hypothesis. -/
@[stacks 0GWS] #check
  (AlgebraicGeometry.locallyQuasiFinite_of_surjective_of_comp_locallyQuasiFinite :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [AlgebraicGeometry.Surjective f]
      [AlgebraicGeometry.LocallyQuasiFinite (f ≫ g)]
      [AlgebraicGeometry.LocallyOfFiniteType g],
      AlgebraicGeometry.LocallyQuasiFinite g)
