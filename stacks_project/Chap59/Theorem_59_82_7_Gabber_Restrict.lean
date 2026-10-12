/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_82_1
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The identity object of the small étale site. -/
abbrev etaleIdentity (X : Scheme.{u}) : X.Etale :=
  MorphismProperty.Over.mk _ (𝟙 X) inferInstance

/-- The identity étale object is terminal: maps to it are the structure morphisms. -/
def etaleIdentityIsTerminal (X : Scheme.{u}) : IsTerminal (etaleIdentity X) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ MorphismProperty.Over.homMk U.hom)
    (fun U m ↦ sorry)

/-- The chosen terminal object of `X.Etale` is isomorphic to the identity étale object. -/
def etaleTerminalIsoIdentity (X : Scheme.{u}) [HasTerminal X.Etale] :
    terminal X.Etale ≅ etaleIdentity X :=
  terminalIsTerminal.uniqueUpToIso (etaleIdentityIsTerminal X)

/-- Base change of the identity étale object along `i` is the identity étale object of the source. -/
def smallEtalePullback_obj_identity {X Z : Scheme.{u}} (i : Z ⟶ X) :
    (smallEtalePullback i).obj (etaleIdentity X) ≅ etaleIdentity Z :=
  MorphismProperty.Over.isoMk
    { hom := pullback.snd (𝟙 X) i
      inv := pullback.lift i (𝟙 Z) sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- Base change of the chosen terminal étale object along `i` is the chosen terminal étale
object of the source. -/
def smallEtalePullback_obj_terminal {X Z : Scheme.{u}} (i : Z ⟶ X)
    [HasTerminal X.Etale] [HasTerminal Z.Etale] :
    (smallEtalePullback i).obj (terminal X.Etale) ≅ terminal Z.Etale :=
  (smallEtalePullback i).mapIso (etaleTerminalIsoIdentity X) ≪≫
    smallEtalePullback_obj_identity i ≪≫ (etaleTerminalIsoIdentity Z).symm

/-- `etaleAbelianRestriction` is additive. -/
instance etaleAbelianRestriction_additive {X Z : Scheme.{u}} (i : Z ⟶ X)
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    (etaleAbelianRestriction i).Additive :=
  sorry

/-- Inverse image of abelian étale sheaves preserves homology. -/
instance etaleAbelianRestriction_preservesHomology {X Z : Scheme.{u}} (i : Z ⟶ X)
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    (etaleAbelianRestriction i).PreservesHomology :=
  sorry

/-- Inverse image of abelian étale sheaves preserves injective objects. -/
instance etaleAbelianRestriction_preservesInjectiveObjects {X Z : Scheme.{u}} (i : Z ⟶ X)
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    (etaleAbelianRestriction i).PreservesInjectiveObjects :=
  sorry

/-- Derived sections of `i^*` are additive. -/
instance etaleAbelianRestriction_comp_sections_additive {X Z : Scheme.{u}} (i : Z ⟶ X)
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [HasTerminal Z.Etale]
    [(siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive]
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    (etaleAbelianRestriction i ⋙
        siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive :=
  sorry

/-- Natural comparison of abelian global sections
`Γ(X_étale, F) ⟶ Γ(Z_étale, i^* F)` via the adjunction unit and the terminal identification. -/
def etaleAbelianSectionsRestrict {X Z : Scheme.{u}} (i : Z ⟶ X)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [HasTerminal X.Etale] [HasTerminal Z.Etale]
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint] :
    siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale) ⟶
      etaleAbelianRestriction i ⋙
        siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale) where
  app F :=
    ((Adjunction.ofIsRightAdjoint
          ((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
            X.smallEtaleTopology Z.smallEtaleTopology)).unit.app F).hom.app
        (op (terminal X.Etale)) ≫
      ((etaleAbelianRestriction i).obj F).obj.map
        (op (smallEtalePullback_obj_terminal i).inv)
  naturality _ _ _ := sorry

/-- Canonical comparison morphism `H^q(X, F) ⟶ H^q(Z, i^* F)` on étale cohomology. -/
def etaleCohomologyRestrict {X Z : Scheme.{u}} (i : Z ⟶ X)
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
    [(etaleAbelianRestriction i).Additive]
    [(etaleAbelianRestriction i).PreservesHomology]
    [(etaleAbelianRestriction i).PreservesInjectiveObjects]
    [(etaleAbelianRestriction i ⋙
        siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    etaleCohomology X F q ⟶
      etaleCohomology Z ((etaleAbelianRestriction i).obj F) q :=
  (NatTrans.rightDerived (etaleAbelianSectionsRestrict i) q).app F ≫
    (Functor.RightDerived.precompObjIso (etaleAbelianRestriction i)
        (siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)) q F).hom

/-- Evaluating `etaleCohomologyRestrict` recovers the derived adjunction-unit comparison
followed by the precomposition identification of derived sections. -/
theorem etaleCohomologyRestrict_eq {X Z : Scheme.{u}} (i : Z ⟶ X)
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
    [(etaleAbelianRestriction i).Additive]
    [(etaleAbelianRestriction i).PreservesHomology]
    [(etaleAbelianRestriction i).PreservesInjectiveObjects]
    [(etaleAbelianRestriction i ⋙
        siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    etaleCohomologyRestrict i F q =
      (NatTrans.rightDerived (etaleAbelianSectionsRestrict i) q).app F ≫
        (Functor.RightDerived.precompObjIso (etaleAbelianRestriction i)
            (siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)) q F).hom :=
  sorry

end AlgebraicGeometry.Scheme.Etale
