module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import stacks_project.Chap103.Lemma_103_15_1_Ringed
public import stacks_project.Chap103.«103_15_2_1_Map»

/-!
# Abelian and derived base-change maps of the 103.15.1 square

A smooth (resp. flat) morphism of algebraic stacks induces a canonical abelian
comparison `g⁻¹ f_* ⟶ f'_*(g')⁻¹` as the mate of the inverse-image 2-cell of
`lisseEtaleMap_comp_ι` (resp. `flatFppfMap_comp_ι`). The degree-`p` map
`g⁻¹ (R^p f_* F) ⟶ R^p f'_*((g')⁻¹ F)` is obtained by postcomposition,
`NatTrans.rightDerived`, and precomposition.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor CategoryTheory.Abelian
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- Pointwise right Kan extensions along `(toFunctor f).op` exist on abelian
presheaves. -/
instance toFunctor_op_hasPointwiseRightKanExtension_addCommGrpCat (f : X ⟶ Y)
    (P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (toFunctor f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The composite of a lisse-étale inclusion with a total functor is continuous. -/
instance lisseEtaleInclusion_comp_toFunctor_isContinuous (f : X ⟶ Y) [Smooth f] :
    (lisseEtaleInclusion X ⋙ toFunctor f).IsContinuous
      (lisseEtaleTopology X) Y.etaleTopology :=
  Functor.isContinuous_comp (lisseEtaleInclusion X) (toFunctor f)
    (lisseEtaleTopology X) X.etaleTopology Y.etaleTopology

/-- The composite of a flat-fppf inclusion with a total functor is continuous. -/
instance flatFppfInclusion_comp_toFunctor_isContinuous (f : X ⟶ Y) [Flat f] :
    (flatFppfInclusion X ⋙ toFunctor f).IsContinuous
      (flatFppfTopology X) (inheritedFppfTopology Y) :=
  Functor.isContinuous_comp (flatFppfInclusion X) (toFunctor f)
    (flatFppfTopology X) (inheritedFppfTopology X) (inheritedFppfTopology Y)

/-- Cocontinuous abelian pushforward along `toFunctor f` on associated étale
sites is additive. -/
instance toFunctor_sheafPushforwardCocontinuous_etale_additive (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      X.etaleTopology Y.etaleTopology).Additive :=
  sorry

/-- Cocontinuous abelian pushforward along `toFunctor f` on inherited fppf
sites is additive. -/
instance toFunctor_sheafPushforwardCocontinuous_inheritedFppf_additive (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (inheritedFppfTopology X) (inheritedFppfTopology Y)).Additive :=
  sorry

section Smooth

variable (f : X ⟶ Y) [Smooth f]

/-- The inverse-image 2-cell `(f')⁻¹ g⁻¹ ⟶ (g')⁻¹ f⁻¹` of the lisse-étale
functoriality square, on abelian sheaves. -/
def lisseEtaleAbelianInverseImageComparison :
    (lisseEtaleInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (lisseEtaleTopology Y) Y.etaleTopology ⋙
      (lisseEtaleMap f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (lisseEtaleTopology X) (lisseEtaleTopology Y) ⟶
      (toFunctor f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        X.etaleTopology Y.etaleTopology ⋙
        (lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (lisseEtaleTopology X) X.etaleTopology :=
  (sheafPushforwardContinuousComp' (lisseEtaleMap_comp_ι f)
      AddCommGrpCat.{u + 1} (lisseEtaleTopology X)
      (lisseEtaleTopology Y) Y.etaleTopology).hom ≫
    (sheafPushforwardContinuousComp (lisseEtaleInclusion X) (toFunctor f)
      AddCommGrpCat.{u + 1} (lisseEtaleTopology X)
      X.etaleTopology Y.etaleTopology).inv

/-- `lisseEtaleAbelianInverseImageComparison` is the composite of
`sheafPushforwardContinuousComp'` along `lisseEtaleMap_comp_ι` with the inverse
of `sheafPushforwardContinuousComp`. -/
theorem lisseEtaleAbelianInverseImageComparison_eq :
    lisseEtaleAbelianInverseImageComparison f =
      (sheafPushforwardContinuousComp' (lisseEtaleMap_comp_ι f)
          AddCommGrpCat.{u + 1} (lisseEtaleTopology X)
          (lisseEtaleTopology Y) Y.etaleTopology).hom ≫
        (sheafPushforwardContinuousComp (lisseEtaleInclusion X) (toFunctor f)
          AddCommGrpCat.{u + 1} (lisseEtaleTopology X)
          X.etaleTopology Y.etaleTopology).inv :=
  sorry

/-- The canonical abelian comparison `g⁻¹ f_* ⟶ f'_*(g')⁻¹` of the lisse-étale
functoriality square. -/
def lisseEtaleAbelianPushforwardRestrictionComparison :
    (toFunctor f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        X.etaleTopology Y.etaleTopology ⋙
      (lisseEtaleInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (lisseEtaleTopology Y) Y.etaleTopology ⟶
      (lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (lisseEtaleTopology X) X.etaleTopology ⋙
        (lisseEtaleMap f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (lisseEtaleTopology X) (lisseEtaleTopology Y) :=
  mateEquiv
    ((toFunctor f).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      X.etaleTopology Y.etaleTopology)
    ((lisseEtaleMap f).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (lisseEtaleTopology X) (lisseEtaleTopology Y))
    (lisseEtaleAbelianInverseImageComparison f)

/-- `lisseEtaleAbelianPushforwardRestrictionComparison` is the mate of
`lisseEtaleAbelianInverseImageComparison` along the cocontinuous sheaf
adjunctions of `toFunctor f` and `lisseEtaleMap f`. -/
theorem lisseEtaleAbelianPushforwardRestrictionComparison_eq :
    lisseEtaleAbelianPushforwardRestrictionComparison f =
      mateEquiv
        ((toFunctor f).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
          X.etaleTopology Y.etaleTopology)
        ((lisseEtaleMap f).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
          (lisseEtaleTopology X) (lisseEtaleTopology Y))
        (lisseEtaleAbelianInverseImageComparison f) :=
  sorry

/-- The canonical abelian lisse-étale comparison `g⁻¹ f_* ⟶ f'_*(g')⁻¹` is an
isomorphism. -/
instance lisseEtaleAbelianPushforwardRestrictionComparison.instIsIso :
    IsIso (lisseEtaleAbelianPushforwardRestrictionComparison f) :=
  sorry

variable [HasSheafify X.etaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify Y.etaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf X.etaleTopology AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1})]

/-- Restriction of abelian étale sheaves along the lisse-étale inclusion of `Y`
preserves homology. -/
instance lisseEtaleInclusion.sheafPushforwardContinuous.instPreservesHomology_target :
    ((lisseEtaleInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (lisseEtaleTopology Y) Y.etaleTopology).PreservesHomology :=
  sorry

/-- Restriction of abelian étale sheaves along the lisse-étale inclusion of `X`
preserves homology. -/
instance lisseEtaleInclusion.sheafPushforwardContinuous.instPreservesHomology_source :
    ((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (lisseEtaleTopology X) X.etaleTopology).PreservesHomology :=
  sorry

/-- Restriction of abelian étale sheaves along the lisse-étale inclusion of `X`
preserves injective objects. -/
instance lisseEtaleInclusion.sheafPushforwardContinuous.instPreservesInjectiveObjects :
    ((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (lisseEtaleTopology X) X.etaleTopology).PreservesInjectiveObjects :=
  sorry

/-- The canonical degree-`p` base-change map
`g⁻¹ (R^p f_* F) ⟶ R^p f'_*((g')⁻¹ F)` of the lisse-étale functoriality
square. -/
def lisseEtaleHigherDirectImageRestrictionComparison
    (F : Sheaf X.etaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) :
    ((lisseEtaleInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (lisseEtaleTopology Y) Y.etaleTopology).obj
      ((((toFunctor f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          X.etaleTopology Y.etaleTopology).rightDerived p).obj F) ⟶
      ((lisseEtalePushforward f).rightDerived p).obj
        (((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (lisseEtaleTopology X) X.etaleTopology).obj F) :=
  (RightDerived.postcompObjIso
      ((toFunctor f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        X.etaleTopology Y.etaleTopology)
      ((lisseEtaleInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (lisseEtaleTopology Y) Y.etaleTopology)
      p F).inv ≫
    (NatTrans.rightDerived (lisseEtaleAbelianPushforwardRestrictionComparison f) p).app F ≫
      (RightDerived.precompObjIso
        ((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (lisseEtaleTopology X) X.etaleTopology)
        (lisseEtalePushforward f) p F).hom

/-- `lisseEtaleHigherDirectImageRestrictionComparison` is the composite of
`RightDerived.postcompObjIso.inv`, `NatTrans.rightDerived` of the abelian
comparison, and `RightDerived.precompObjIso.hom`. -/
theorem lisseEtaleHigherDirectImageRestrictionComparison_eq
    (F : Sheaf X.etaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) :
    lisseEtaleHigherDirectImageRestrictionComparison f F p =
      (RightDerived.postcompObjIso
          ((toFunctor f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
            X.etaleTopology Y.etaleTopology)
          ((lisseEtaleInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (lisseEtaleTopology Y) Y.etaleTopology)
          p F).inv ≫
        (NatTrans.rightDerived (lisseEtaleAbelianPushforwardRestrictionComparison f)
            p).app F ≫
          (RightDerived.precompObjIso
            ((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (lisseEtaleTopology X) X.etaleTopology)
            (lisseEtalePushforward f) p F).hom :=
  sorry

end Smooth

section Flat

variable (f : X ⟶ Y) [Flat f]

/-- The inverse-image 2-cell `(f')⁻¹ g⁻¹ ⟶ (g')⁻¹ f⁻¹` of the flat-fppf
functoriality square, on abelian sheaves. -/
def flatFppfAbelianInverseImageComparison :
    (flatFppfInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (flatFppfTopology Y) (inheritedFppfTopology Y) ⋙
      (flatFppfMap f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (flatFppfTopology X) (flatFppfTopology Y) ⟶
      (toFunctor f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (inheritedFppfTopology X) (inheritedFppfTopology Y) ⋙
        (flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (flatFppfTopology X) (inheritedFppfTopology X) :=
  (sheafPushforwardContinuousComp' (flatFppfMap_comp_ι f)
      AddCommGrpCat.{u + 1} (flatFppfTopology X)
      (flatFppfTopology Y) (inheritedFppfTopology Y)).hom ≫
    (sheafPushforwardContinuousComp (flatFppfInclusion X) (toFunctor f)
      AddCommGrpCat.{u + 1} (flatFppfTopology X)
      (inheritedFppfTopology X) (inheritedFppfTopology Y)).inv

/-- `flatFppfAbelianInverseImageComparison` is the composite of
`sheafPushforwardContinuousComp'` along `flatFppfMap_comp_ι` with the inverse of
`sheafPushforwardContinuousComp`. -/
theorem flatFppfAbelianInverseImageComparison_eq :
    flatFppfAbelianInverseImageComparison f =
      (sheafPushforwardContinuousComp' (flatFppfMap_comp_ι f)
          AddCommGrpCat.{u + 1} (flatFppfTopology X)
          (flatFppfTopology Y) (inheritedFppfTopology Y)).hom ≫
        (sheafPushforwardContinuousComp (flatFppfInclusion X) (toFunctor f)
          AddCommGrpCat.{u + 1} (flatFppfTopology X)
          (inheritedFppfTopology X) (inheritedFppfTopology Y)).inv :=
  sorry

/-- The canonical abelian comparison `g⁻¹ f_* ⟶ f'_*(g')⁻¹` of the flat-fppf
functoriality square. -/
def flatFppfAbelianPushforwardRestrictionComparison :
    (toFunctor f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (inheritedFppfTopology X) (inheritedFppfTopology Y) ⋙
      (flatFppfInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (flatFppfTopology Y) (inheritedFppfTopology Y) ⟶
      (flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (flatFppfTopology X) (inheritedFppfTopology X) ⋙
        (flatFppfMap f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (flatFppfTopology X) (flatFppfTopology Y) :=
  mateEquiv
    ((toFunctor f).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (inheritedFppfTopology X) (inheritedFppfTopology Y))
    ((flatFppfMap f).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (flatFppfTopology X) (flatFppfTopology Y))
    (flatFppfAbelianInverseImageComparison f)

/-- `flatFppfAbelianPushforwardRestrictionComparison` is the mate of
`flatFppfAbelianInverseImageComparison` along the cocontinuous sheaf adjunctions
of `toFunctor f` and `flatFppfMap f`. -/
theorem flatFppfAbelianPushforwardRestrictionComparison_eq :
    flatFppfAbelianPushforwardRestrictionComparison f =
      mateEquiv
        ((toFunctor f).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
          (inheritedFppfTopology X) (inheritedFppfTopology Y))
        ((flatFppfMap f).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
          (flatFppfTopology X) (flatFppfTopology Y))
        (flatFppfAbelianInverseImageComparison f) :=
  sorry

/-- The canonical abelian flat-fppf comparison `g⁻¹ f_* ⟶ f'_*(g')⁻¹` is an
isomorphism. -/
instance flatFppfAbelianPushforwardRestrictionComparison.instIsIso :
    IsIso (flatFppfAbelianPushforwardRestrictionComparison f) :=
  sorry

variable [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (inheritedFppfTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (flatFppfTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1})]

/-- Restriction of abelian inherited-fppf sheaves along the flat-fppf inclusion
of `Y` preserves homology. -/
instance flatFppfInclusion.sheafPushforwardContinuous.instPreservesHomology_target :
    ((flatFppfInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (flatFppfTopology Y) (inheritedFppfTopology Y)).PreservesHomology :=
  sorry

/-- Restriction of abelian inherited-fppf sheaves along the flat-fppf inclusion
of `X` preserves homology. -/
instance flatFppfInclusion.sheafPushforwardContinuous.instPreservesHomology_source :
    ((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (flatFppfTopology X) (inheritedFppfTopology X)).PreservesHomology :=
  sorry

/-- Restriction of abelian inherited-fppf sheaves along the flat-fppf inclusion
of `X` preserves injective objects. -/
instance flatFppfInclusion.sheafPushforwardContinuous.instPreservesInjectiveObjects :
    ((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (flatFppfTopology X) (inheritedFppfTopology X)).PreservesInjectiveObjects :=
  sorry

/-- The canonical degree-`p` base-change map
`g⁻¹ (R^p f_* F) ⟶ R^p f'_*((g')⁻¹ F)` of the flat-fppf functoriality square. -/
def flatFppfHigherDirectImageRestrictionComparison
    (F : Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    ((flatFppfInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (flatFppfTopology Y) (inheritedFppfTopology Y)).obj
      ((((toFunctor f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (inheritedFppfTopology X) (inheritedFppfTopology Y)).rightDerived p).obj F) ⟶
      ((flatFppfPushforward f).rightDerived p).obj
        (((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (flatFppfTopology X) (inheritedFppfTopology X)).obj F) :=
  (RightDerived.postcompObjIso
      ((toFunctor f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (inheritedFppfTopology X) (inheritedFppfTopology Y))
      ((flatFppfInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (flatFppfTopology Y) (inheritedFppfTopology Y))
      p F).inv ≫
    (NatTrans.rightDerived (flatFppfAbelianPushforwardRestrictionComparison f) p).app F ≫
      (RightDerived.precompObjIso
        ((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (flatFppfTopology X) (inheritedFppfTopology X))
        (flatFppfPushforward f) p F).hom

/-- `flatFppfHigherDirectImageRestrictionComparison` is the composite of
`RightDerived.postcompObjIso.inv`, `NatTrans.rightDerived` of the abelian
comparison, and `RightDerived.precompObjIso.hom`. -/
theorem flatFppfHigherDirectImageRestrictionComparison_eq
    (F : Sheaf (inheritedFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    flatFppfHigherDirectImageRestrictionComparison f F p =
      (RightDerived.postcompObjIso
          ((toFunctor f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
            (inheritedFppfTopology X) (inheritedFppfTopology Y))
          ((flatFppfInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (flatFppfTopology Y) (inheritedFppfTopology Y))
          p F).inv ≫
        (NatTrans.rightDerived (flatFppfAbelianPushforwardRestrictionComparison f)
            p).app F ≫
          (RightDerived.precompObjIso
            ((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (flatFppfTopology X) (inheritedFppfTopology X))
            (flatFppfPushforward f) p F).hom :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicStack
