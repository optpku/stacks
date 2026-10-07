module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.StalkBaseChange

open CategoryTheory AlgebraicGeometry

universe u

/- Remark 59.53.2: the canonical maps from the geometric stalk of a derived direct image to
derived sections on the pointed strict-henselian base change and then to the geometric fiber
compose to the usual geometric-fiber base-change map. -/
@[stacks 0GIX] #check
  (AlgebraicGeometry.Scheme.Etale.Cohomology.etaleStalkBaseChange_factorization :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (s : Scheme.GeometricPoint S)
      (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      Scheme.Etale.Cohomology.etaleStalkToStrictHenselizationCohomology f s K ≫
          Scheme.Etale.Cohomology.strictHenselizationToGeometricFiberCohomology f s K =
        Scheme.Etale.Cohomology.etaleStalkToGeometricFiberBaseChange f s K)
