/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_27_0_4_Comparison»
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- 66.27.0.3: if `f : ofOver U ⟶ Y` is étale of algebraic spaces and `X` is a scheme, then
`X` is an object of `Y_étale` as `smallEtaleSite.mk f`, and the identification
`X_étale = Y_étale / X` is the existing `IsEquivalence` of
`etaleLocalizationFunctor : smallEtaleSite (ofOver U) ⥤ Over (smallEtaleSite.mk f)`
(not definitional equality of categories, and not the ringed iso `etaleLocalizationIso`).
The slice site `Y_étale / X` is `Over (smallEtaleSite.mk f)` with topology
`(smallEtaleTopology Y).over (smallEtaleSite.mk f)`. -/
@[stacks 04M0] #check
  (etaleLocalizationFunctor.instIsEquivalence :
    ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S} (f : ofOver U ⟶ Y) [Etale f],
      (etaleLocalizationFunctor f).IsEquivalence)
