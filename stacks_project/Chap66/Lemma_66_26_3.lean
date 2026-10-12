/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_26_3_Glueing
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.26.3: an 𝒪_X-module on X_étale is equivalently the data of an 𝒪_U-module F_U
on U_étale for every U in Ob(X_étale), together with module isomorphisms
c_f : f_small^* F_U ≅ F_{U'} for morphisms f : U' ⟶ U in X_étale, subject to the cocycle
c_g ∘ g_small^* c_f = c_{f ∘ g}. -/
@[stacks 03LY] #check
  (SmallEtaleModuleGlueing.fromModules_isEquivalence :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      Functor.IsEquivalence (SmallEtaleModuleGlueing.fromModules X))
