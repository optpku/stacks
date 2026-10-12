/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import stacks_project.Chap59.Proposition_59_54_2_Leray_spectral_sequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}}
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal S.Etale]
variable [(siteAbelianSectionsFunctor S.smallEtaleTopology (terminal S.Etale)).Additive]

/-- Induced map on étale cohomology of abelian sheaves along a morphism of sheaves. -/
def etaleCohomology_map {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) :
    etaleCohomology S F n ⟶ etaleCohomology S G n :=
  ((siteAbelianSectionsFunctor S.smallEtaleTopology (terminal S.Etale)).rightDerived n).map φ

/-- Evaluating `etaleCohomology_map` recovers the right-derived sections functor on morphisms. -/
theorem etaleCohomology_map_eq {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) :
    etaleCohomology_map φ n =
      ((siteAbelianSectionsFunctor S.smallEtaleTopology (terminal S.Etale)).rightDerived n).map φ :=
  sorry

/-- Restriction of an abelian sheaf along a morphism of schemes on small étale sites. -/
noncomputable abbrev etaleAbelianRestriction {X Z : Scheme.{u}} (i : Z ⟶ X)
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} :=
  (smallEtalePullback i).sheafPullback AddCommGrpCat.{u}
    X.smallEtaleTopology Z.smallEtaleTopology

/-- Evaluating restriction recovers sheaf pullback along `smallEtalePullback`. -/
theorem etaleAbelianRestriction_eq {X Z : Scheme.{u}} (i : Z ⟶ X)
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    etaleAbelianRestriction i =
      (smallEtalePullback i).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology :=
  sorry

/-- Lemma 59.82.1: a positive-degree étale cohomology class of a torsion abelian
sheaf on a closed subscheme of an affine scheme is killed after an injective
extension of torsion abelian sheaves on `X_étale`. -/
@[stacks 09ZE]
theorem exists_injective_locallyTorsion_etaleCohomology_eq_zero
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
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
      (etaleCohomology Z ((etaleAbelianRestriction i).obj F) q)) :
    ∃ (F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (φ : F ⟶ F'),
      Mono φ ∧ Sheaf.IsLocallyTorsion F' ∧
        (CategoryTheory.forget AddCommGrpCat).map
            (etaleCohomology_map ((etaleAbelianRestriction i).map φ) q) ξ = 0 :=
  sorry

end AlgebraicGeometry.Scheme.Etale
