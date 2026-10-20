module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Effacement
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 59.82.1: a positive-degree étale cohomology class of a torsion abelian
sheaf on a closed subscheme of an affine scheme is killed after an injective
extension of torsion abelian sheaves on `X_étale`. -/
@[stacks 09ZE] #check
  (AlgebraicGeometry.Scheme.Etale.exists_injective_locallyTorsion_etaleCohomology_eq_zero :
    ∀ {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X.Etale]
    [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal Z.Etale]
    [(siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive]
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hF : Sheaf.IsLocallyTorsion F) {q : ℕ} (hq : 0 < q)
    (ξ : (CategoryTheory.forget AddCommGrpCat).obj
      (etaleCohomology Z ((etaleAbelianRestriction i).obj F) q)),
    ∃ (F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (φ : F ⟶ F'),
      Mono φ ∧ Sheaf.IsLocallyTorsion F' ∧
        (CategoryTheory.forget AddCommGrpCat).map
            (etaleCohomology_map ((etaleAbelianRestriction i).map φ) q) ξ = 0)

end AlgebraicGeometry.Scheme.Etale
