/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.OpenImmersion

/-!
# Directed systems of compact-support étale pushforwards

The covariance diagrams, cocones, and colimit comparisons identifying `f_! F`
with a directed colimit of `f_{i,!}(F|_{X_i})` along an inclusion-directed
Zariski open covering of the source.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/-- The index type of a family of opens, equipped with the inclusion preorder
`i ≤ j ↔ U i ≤ U j`. Marked irreducible so the inclusion order is not
confused with a preorder on the raw index type. -/
irreducible_def OpensInclusionIndex {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens) : Type v :=
  (fun _ : ι → X.Opens ↦ ι) U

/-- The underlying index of an object of `OpensInclusionIndex U`. -/
def OpensInclusionIndex.asIndex {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens}
    (i : OpensInclusionIndex U) : ι :=
  Eq.mp (OpensInclusionIndex_def U) i

/-- Inclusion of opens induces a preorder on `OpensInclusionIndex U`. -/
instance instPreorderOpensInclusionIndex {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) : Preorder (OpensInclusionIndex U) where
  le i j := U i.asIndex ≤ U j.asIndex
  le_refl i := le_rfl
  le_trans i j k := le_trans

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]

/-- The compact-support pushforward of the restriction of `F` to a Zariski open
of the source. -/
def etaleLowerShriekOpensObj (U : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (etaleLowerShriek (U.ι ≫ f)).obj ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F)

/-- The covariance map
`f_{U,!}(F|_U) ⟶ f_{V,!}(F|_V)` along an inclusion `U ≤ V` of Zariski opens. -/
def etaleLowerShriekOpensMap {U V : X.Opens} (hUV : U ≤ V)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekOpensObj f U F ⟶ etaleLowerShriekOpensObj f V F :=
  let e :=
    (congrArg (fun g : (U : Scheme.{u}) ⟶ X ↦ g ≫ f) (X.homOfLE_ι hUV).symm).trans
      (Category.assoc (X.homOfLE hUV) V.ι f)
  let restrictionCongr {j j' : (U : Scheme.{u}) ⟶ X} [Etale j] [Etale j']
      (hjj' : j = j') :
      etaleRestrictionSheaf j AddCommGrpCat.{u} ≅
        etaleRestrictionSheaf j' AddCommGrpCat.{u} :=
    eqToIso (hjj' ▸ rfl)
  (etaleLowerShriekCongr e).hom.app ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F) ≫
    (etaleLowerShriek (X.homOfLE hUV ≫ V.ι ≫ f)).map
      ((restrictionCongr (X.homOfLE_ι hUV).symm).hom.app F ≫
        (etaleAbelianRestrictionSheafCompIso V.ι (X.homOfLE hUV)).inv.app F) ≫
    (etaleLowerShriekOpenImmersion (X.homOfLE hUV) (V.ι ≫ f)).app
      ((etaleRestrictionSheaf V.ι AddCommGrpCat.{u}).obj F)

/-- Covariance along the identity inclusion of an open is the identity map. -/
theorem etaleLowerShriekOpensMap_id (U : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekOpensMap f (le_refl U) F = 𝟙 (etaleLowerShriekOpensObj f U F) :=
  sorry

/-- Covariance along a composite inclusion of opens is the composite of the
covariance maps. -/
theorem etaleLowerShriekOpensMap_comp {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekOpensMap f (hUV.trans hVW) F =
      etaleLowerShriekOpensMap f hUV F ≫ etaleLowerShriekOpensMap f hVW F :=
  sorry

variable {ι : Type v} (U : ι → X.Opens)

/-- The directed system `i ↦ f_{i,!}(F|_{X_i})` on the inclusion preorder of `U`,
with transition maps given by covariance along open immersions. -/
def etaleLowerShriekDirectedDiagram
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    OpensInclusionIndex U ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  obj i := etaleLowerShriekOpensObj f (U i.asIndex) F
  map {i j} g := etaleLowerShriekOpensMap f (CategoryTheory.leOfHom g : i ≤ j) F
  map_id i := etaleLowerShriekOpensMap_id f (U i.asIndex) F
  map_comp {i j k} g h := etaleLowerShriekOpensMap_comp f
    (CategoryTheory.leOfHom g : i ≤ j) (CategoryTheory.leOfHom h : j ≤ k) F

/-- The object of the directed system at `i` is `f_{i,!}(F|_{U i})`. -/
theorem etaleLowerShriekDirectedDiagram_obj
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (i : OpensInclusionIndex U) :
    (etaleLowerShriekDirectedDiagram f U F).obj i =
      etaleLowerShriekOpensObj f (U i.asIndex) F :=
  rfl

/-- Transition maps of the directed system are the covariance maps along the
underlying inclusions. -/
theorem etaleLowerShriekDirectedDiagram_map
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {i j : OpensInclusionIndex U} (g : i ⟶ j) :
    (etaleLowerShriekDirectedDiagram f U F).map g =
      etaleLowerShriekOpensMap f (CategoryTheory.leOfHom g : i ≤ j) F :=
  rfl

/-- Covariance into the full source is compatible with every transition in
the diagram of opens. -/
theorem etaleLowerShriekDirectedCocone_naturality
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {i j : OpensInclusionIndex U} (g : i ⟶ j) :
    (etaleLowerShriekDirectedDiagram f U F).map g ≫
        (etaleLowerShriekOpenImmersion_opens (U j.asIndex) f).app F =
      (etaleLowerShriekOpenImmersion_opens (U i.asIndex) f).app F ≫
        𝟙 ((etaleLowerShriek f).obj F) :=
  sorry

/-- The covariance cocone from `i ↦ f_{i,!}(F|_{X_i})` to `f_! F`, with legs
`etaleLowerShriekOpenImmersion_opens`. -/
def etaleLowerShriekDirectedCocone
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Cocone (etaleLowerShriekDirectedDiagram f U F) where
  pt := (etaleLowerShriek f).obj F
  ι :=
    { app := fun i ↦ (etaleLowerShriekOpenImmersion_opens (U i.asIndex) f).app F
      naturality := fun i j g ↦ etaleLowerShriekDirectedCocone_naturality f U F g }

/-- The apex of the covariance cocone is `f_! F`. -/
theorem etaleLowerShriekDirectedCocone_pt
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriekDirectedCocone f U F).pt = (etaleLowerShriek f).obj F :=
  rfl

/-- Cocone legs are the covariance maps into `f_! F`. -/
theorem etaleLowerShriekDirectedCocone_ι
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (i : OpensInclusionIndex U) :
    (etaleLowerShriekDirectedCocone f U F).ι.app i =
      (etaleLowerShriekOpenImmersion_opens (U i.asIndex) f).app F :=
  rfl

/-- The canonical comparison `colim_i f_{i,!}(F|_{X_i}) ⟶ f_! F` induced by the
covariance cocone. -/
def etaleLowerShriekDirectedComparisonApp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [HasColimit (etaleLowerShriekDirectedDiagram f U F)] :
    colimit (etaleLowerShriekDirectedDiagram f U F) ⟶ (etaleLowerShriek f).obj F :=
  colimit.desc (etaleLowerShriekDirectedDiagram f U F)
    (etaleLowerShriekDirectedCocone f U F)

/-- The comparison morphism is `colimit.desc` of the covariance cocone. -/
theorem etaleLowerShriekDirectedComparisonApp_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [HasColimit (etaleLowerShriekDirectedDiagram f U F)] :
    etaleLowerShriekDirectedComparisonApp f U F =
      colimit.desc (etaleLowerShriekDirectedDiagram f U F)
        (etaleLowerShriekDirectedCocone f U F) :=
  rfl

/-- Morphisms of coefficient sheaves commute with covariance along inclusions
in the diagram of opens. -/
theorem etaleLowerShriekDirectedDiagramMap_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G)
    {i j : OpensInclusionIndex U} (g : i ⟶ j) :
    (etaleLowerShriekDirectedDiagram f U F).map g ≫
        (etaleLowerShriek ((U j.asIndex).ι ≫ f)).map
          ((etaleRestrictionSheaf (U j.asIndex).ι AddCommGrpCat.{u}).map α) =
      (etaleLowerShriek ((U i.asIndex).ι ≫ f)).map
          ((etaleRestrictionSheaf (U i.asIndex).ι AddCommGrpCat.{u}).map α) ≫
        (etaleLowerShriekDirectedDiagram f U G).map g :=
  sorry

/-- A morphism of abelian étale sheaves induces a morphism of directed
compact-support diagrams. -/
def etaleLowerShriekDirectedDiagramMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    etaleLowerShriekDirectedDiagram f U F ⟶ etaleLowerShriekDirectedDiagram f U G where
  app i :=
    (etaleLowerShriek ((U i.asIndex).ι ≫ f)).map
      ((etaleRestrictionSheaf (U i.asIndex).ι AddCommGrpCat.{u}).map α)
  naturality := fun i j g ↦ etaleLowerShriekDirectedDiagramMap_naturality f U α g

/-- The comparison `colim_i f_{i,!}(F|_{X_i}) ⟶ f_! F` is natural in `F`. -/
theorem etaleLowerShriekDirectedComparisonApp_natural
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G)
    [HasColimit (etaleLowerShriekDirectedDiagram f U F)]
    [HasColimit (etaleLowerShriekDirectedDiagram f U G)] :
    colimMap (etaleLowerShriekDirectedDiagramMap f U α) ≫
        etaleLowerShriekDirectedComparisonApp f U G =
      etaleLowerShriekDirectedComparisonApp f U F ≫ (etaleLowerShriek f).map α :=
  sorry

/-- For an inclusion-directed open cover, the canonical comparison from the
colimit of restricted compact-support pushforwards is an isomorphism. -/
theorem etaleLowerShriekDirectedComparison_isIso_of_openCover
    (hcover : IsOpenCover U) (hdir : Directed (· ≤ ·) U)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [HasColimit (etaleLowerShriekDirectedDiagram f U F)] :
    IsIso (etaleLowerShriekDirectedComparisonApp f U F) :=
  sorry

/-- The comparison from the directed colimit over an open cover to the
compact-support pushforward is canonically an isomorphism. -/
instance etaleLowerShriekDirectedComparison_isIso
    [Fact (IsOpenCover U)] [Fact (Directed (· ≤ ·) U)]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [HasColimit (etaleLowerShriekDirectedDiagram f U F)] :
    IsIso (etaleLowerShriekDirectedComparisonApp f U F) :=
  etaleLowerShriekDirectedComparison_isIso_of_openCover f U Fact.out Fact.out F

end AlgebraicGeometry.Scheme.Etale

end
