/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.TopologicalInvariance
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.TopologicalInvariance
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

/- Proposition 59.45.4 (Topological invariance of étale cohomology) (1):
a universal homeomorphism identifies the small étale sites, including their
covering sieves. -/
@[stacks 03SI] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback_isDenseSubsite_of_universalHomeomorphism :
    ∀ {X0 X : Scheme.{u}} (f : X0 ⟶ X) [UniversalHomeomorphism f],
      Functor.IsDenseSubsite X.smallEtaleTopology X0.smallEtaleTopology
        (smallEtalePullback f))

#check
  (AlgebraicGeometry.Scheme.smallEtalePullback_isEquivalence_of_universalHomeomorphism :
    ∀ {X0 X : Scheme.{u}} (f : X0 ⟶ X) [UniversalHomeomorphism f],
      (AlgebraicGeometry.Scheme.smallEtalePullback f).IsEquivalence)

/- Proposition 59.45.4 (Topological invariance of étale cohomology) (2):
a universal homeomorphism identifies the étale topoi. -/
@[stacks 03SI] #check
  (AlgebraicGeometry.Scheme.smallEtaleSheaf_isEquivalence_of_universalHomeomorphism
      (Type (u + 1)) :
    ∀ {X0 X : Scheme.{u}} (f : X0 ⟶ X) [UniversalHomeomorphism f],
      ((smallEtalePullback f).sheafPullback (Type (u + 1))
        X.smallEtaleTopology X0.smallEtaleTopology).IsEquivalence)

/- Proposition 59.45.4 (Topological invariance of étale cohomology) (3):
étale cohomology of an abelian sheaf is identified with that of its restriction
along a universal homeomorphism. -/
@[stacks 03SI] #check
  (AlgebraicGeometry.Scheme.etaleCohomologyRestrictionIso :
    ∀ {X0 X : Scheme.{u}} (f : X0 ⟶ X) [UniversalHomeomorphism f]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ),
      (Sheaf.functorH.{u + 1} X.smallEtaleTopology q).obj F ≅
        (Sheaf.functorH.{u + 1} X0.smallEtaleTopology q).obj
          (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
            X.smallEtaleTopology X0.smallEtaleTopology).obj F))

end
