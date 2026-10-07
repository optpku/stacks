module

public import stacks_project.Chap66.Lemma_66_29_3_Glueing
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.29.3: a quasi-coherent 𝒪_X-module on X_étale is equivalently the data of a
quasi-coherent 𝒪_U-module F_U on U_étale for every U in Ob(X_étale), together with
module isomorphisms c_f : f_small^* F_U ≅ F_{U'} for morphisms f : U' ⟶ U in X_étale,
subject to the cocycle c_g ∘ g_small^* c_f = c_{f ∘ g}. -/
@[stacks 03LZ] #check
  (SmallEtaleQCohGlueing.fromQCoh_isEquivalence :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      Functor.IsEquivalence (SmallEtaleQCohGlueing.fromQCoh X))
