module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Glueing
import StacksCheckRecall

universe u

/- Lemma 66.29.3: a quasi-coherent 𝒪_X-module on X_étale is equivalently the data of a
quasi-coherent 𝒪_U-module F_U on U_étale for every U in Ob(X_étale), together with
module isomorphisms c_f : f_small^* F_U ≅ F_{U'} for morphisms f : U' ⟶ U in X_étale,
subject to the cocycle c_g ∘ g_small^* c_f = c_{f ∘ g}. -/
@[stacks 03LZ] #check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtaleQCohGlueing.fromQCoh_isEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      CategoryTheory.Functor.IsEquivalence (AlgebraicGeometry.AlgebraicSpace.SmallEtaleQCohGlueing.fromQCoh X))
