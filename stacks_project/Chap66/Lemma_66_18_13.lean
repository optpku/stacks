module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Glueing
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.18.13: a sheaf on X_étale is equivalently the data of a sheaf F_U on U_étale
for every U in Ob(X_étale), together with isomorphisms c_f : f_small⁻¹ F_U ≅ F_{U'}
for every f : U' ⟶ U in X_étale, subject to the cocycle
c_g ∘ g_small⁻¹ c_f = c_{f ∘ g}. -/
@[stacks 03LS] #check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtaleGlueing.fromSheaf_isEquivalence :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      Functor.IsEquivalence
        (AlgebraicGeometry.AlgebraicSpace.SmallEtaleGlueing.fromSheaf X))
