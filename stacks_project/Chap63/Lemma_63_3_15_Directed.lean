module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap63.Remark_63_3_5_Covariance_with_respect_to_open_embeddings_OpenImmersion

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

/-- The Remark 63.3.5 covariance map
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

variable {ι : Type v} (U : ι → X.Opens)

/-- The directed system `i ↦ f_{i,!}(F|_{X_i})` on the inclusion preorder of `U`,
with transition maps the covariance maps of Remark 63.3.5. -/
def etaleLowerShriekDirectedDiagram
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    OpensInclusionIndex U ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  obj i := etaleLowerShriekOpensObj f (U i.asIndex) F
  map {i j} g := etaleLowerShriekOpensMap f (CategoryTheory.leOfHom g : i ≤ j) F
  map_id := sorry
  map_comp := sorry

/-- The object of the directed system at `i` is `f_{i,!}(F|_{U i})`. -/
theorem etaleLowerShriekDirectedDiagram_obj
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (i : OpensInclusionIndex U) :
    (etaleLowerShriekDirectedDiagram f U F).obj i =
      etaleLowerShriekOpensObj f (U i.asIndex) F :=
  sorry

/-- Transition maps of the directed system are the Remark 63.3.5 covariance
maps along the underlying inclusions. -/
theorem etaleLowerShriekDirectedDiagram_map
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {i j : OpensInclusionIndex U} (g : i ⟶ j) :
    (etaleLowerShriekDirectedDiagram f U F).map g =
      etaleLowerShriekOpensMap f (CategoryTheory.leOfHom g : i ≤ j) F :=
  sorry

/-- The covariance cocone from `i ↦ f_{i,!}(F|_{X_i})` to `f_! F`, with legs
`etaleLowerShriekOpenImmersion_opens`. -/
def etaleLowerShriekDirectedCocone
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Cocone (etaleLowerShriekDirectedDiagram f U F) where
  pt := (etaleLowerShriek f).obj F
  ι :=
    { app := fun i ↦ (etaleLowerShriekOpenImmersion_opens (U i.asIndex) f).app F
      naturality := sorry }

/-- The apex of the covariance cocone is `f_! F`. -/
theorem etaleLowerShriekDirectedCocone_pt
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriekDirectedCocone f U F).pt = (etaleLowerShriek f).obj F :=
  sorry

/-- Cocone legs are the Remark 63.3.5 covariance maps into `f_! F`. -/
theorem etaleLowerShriekDirectedCocone_ι
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (i : OpensInclusionIndex U) :
    (etaleLowerShriekDirectedCocone f U F).ι.app i =
      (etaleLowerShriekOpenImmersion_opens (U i.asIndex) f).app F :=
  sorry

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
  sorry

/-- A morphism of abelian étale sheaves induces a morphism of directed
compact-support diagrams. -/
def etaleLowerShriekDirectedDiagramMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    etaleLowerShriekDirectedDiagram f U F ⟶ etaleLowerShriekDirectedDiagram f U G where
  app i :=
    (etaleLowerShriek ((U i.asIndex).ι ≫ f)).map
      ((etaleRestrictionSheaf (U i.asIndex).ι AddCommGrpCat.{u}).map α)
  naturality := sorry

/-- The comparison `colim_i f_{i,!}(F|_{X_i}) ⟶ f_! F` is natural in `F`. -/
theorem etaleLowerShriekDirectedComparisonApp_natural
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G)
    [HasColimit (etaleLowerShriekDirectedDiagram f U F)]
    [HasColimit (etaleLowerShriekDirectedDiagram f U G)] :
    colimMap (etaleLowerShriekDirectedDiagramMap f U α) ≫
        etaleLowerShriekDirectedComparisonApp f U G =
      etaleLowerShriekDirectedComparisonApp f U F ≫ (etaleLowerShriek f).map α :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
