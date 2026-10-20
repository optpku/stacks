module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.TorsionDirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 59.78.2 (1): if `f : X ⟶ Y` is quasi-compact and quasi-separated and
`F` is a torsion abelian sheaf on `X_étale`, then `Rⁿ f_* F` is a torsion
abelian sheaf on `Y_étale` for every `n`. -/
@[stacks 0DDD] #check
  (AlgebraicGeometry.Scheme.Etale.higherDirectImage_isLocallyTorsion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsLocallyTorsion F → ∀ n : ℕ,
      IsLocallyTorsion (((etaleAbelianPushforward.{u + 1} f).rightDerived n).obj F))

/- Lemma 59.78.2 (2): if `f : X ⟶ Y` is quasi-compact and quasi-separated and
`K ∈ D⁺(X_étale)` has torsion cohomology sheaves, then `Rf_* K` is an object of
`D⁺(Y_étale)` whose cohomology sheaves are torsion abelian sheaves. -/
@[stacks 0DDD] #check
  (AlgebraicGeometry.Scheme.Etale.derivedPushforward_cohomology_isLocallyTorsion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K →
      DerivedCategory.Plus.cohomologyIn (Sheaf.torsion Y.smallEtaleTopology)
        ((etaleAbelianPushforward.{u + 1} f).rightDerivedFunctorPlus.obj K))

end AlgebraicGeometry.Scheme.Etale
