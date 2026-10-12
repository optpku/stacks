/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap85.Lemma_85_33_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_33_6_Cohomology

/-!
# Čech Hom-group maps for an fppf hypercovering

An augmentation `a : U ⟶ X` determines face maps `d_i : U_1 ⟶ U_0` and the
derived pullbacks `La_n^*`. Restriction along `a_0` and the alternating
difference of the conjugated face pullbacks give the two nonzero arrows of the
Hom sequence in Lemma 85.35.1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace CategoryTheory.Preadditive
open Functor
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}

/-- The degree-`n` morphism `U_n ⟶ X` of an augmentation `a`. -/
def stageMap (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    U.obj (op ⦋n⦌) ⟶ X :=
  a.app (op ⦋n⦌)

/-- `stageMap a n` is the component of `a` at `op ⦋n⦌`. -/
theorem stageMap_eq (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    stageMap a n = a.app (op ⦋n⦌) :=
  sorry

/-- The face map `d_i : U_1 ⟶ U_0` induced by `SimplexCategory.δ i`. -/
def augmentationFace (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    U.obj (op ⦋1⦌) ⟶ U.obj (op ⦋0⦌) :=
  let _ := a
  U.map (SimplexCategory.δ i).op

/-- `augmentationFace a i` is the simplicial operator `U.map (SimplexCategory.δ i).op`. -/
theorem augmentationFace_eq (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    augmentationFace a i = U.map (SimplexCategory.δ i).op :=
  sorry

/-- Each face map equalizes the degree-zero and degree-one augmentations. -/
theorem augmentationFace_comp (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    augmentationFace a i ≫ stageMap a 0 = stageMap a 1 :=
  sorry

/-- The derived-pullback composition comparison for a face and `a_0` is an
isomorphism. -/
theorem augmentationFace_compComparison_isIso
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    IsIso
      (modulePullbackDerived.compComparison
        (augmentationFace a i) (stageMap a 0)) :=
  sorry

/-- The comparison isomorphism
`La_0^* ⋙ L(d_i)^* ≅ L(d_i ≫ a_0)^*`. -/
def augmentationFace_compIso (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    modulePullbackDerived (stageMap a 0) ⋙
        modulePullbackDerived (augmentationFace a i) ≅
      modulePullbackDerived (augmentationFace a i ≫ stageMap a 0) :=
  @asIso _ _ _ _
    (modulePullbackDerived.compComparison
      (augmentationFace a i) (stageMap a 0))
    (augmentationFace_compComparison_isIso a i)

/-- The underlying natural transformation of `augmentationFace_compIso` is the
composition comparison. -/
theorem augmentationFace_compIso_hom
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    (augmentationFace_compIso a i).hom =
      modulePullbackDerived.compComparison
        (augmentationFace a i) (stageMap a 0) :=
  sorry

/-- The identification `La_0^* ⋙ L(d_i)^* ≅ La_1^*` of derived pullbacks. -/
def augmentationFace_pullbackIso
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    modulePullbackDerived (stageMap a 0) ⋙
        modulePullbackDerived (augmentationFace a i) ≅
      modulePullbackDerived (stageMap a 1) :=
  augmentationFace_compIso a i ≪≫
    eqToIso
      (congrArg (fun h : U.obj (op ⦋1⦌) ⟶ X ↦ modulePullbackDerived h)
        (augmentationFace_comp a i))

/-- `augmentationFace_pullbackIso` is the composition comparison followed by
transport along `augmentationFace_comp`. -/
theorem augmentationFace_pullbackIso_eq
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (i : Fin 2) :
    augmentationFace_pullbackIso a i =
      augmentationFace_compIso a i ≪≫
        eqToIso
          (congrArg (fun h : U.obj (op ⦋1⦌) ⟶ X ↦ modulePullbackDerived h)
            (augmentationFace_comp a i)) :=
  sorry

variable {Y : AlgebraicSpace S}

/-- Additivity of derived pullback on Hom-groups. -/
theorem pullbackMapAddHom_map_add (f : Y ⟶ X) (K E : ModuleDerived X)
    (α β : K ⟶ E) :
    (modulePullbackDerived f).map (α + β) =
      (modulePullbackDerived f).map α + (modulePullbackDerived f).map β :=
  sorry

/-- The additive map on Hom-groups induced by derived pullback `Lf^*`. -/
def pullbackMapAddHom (f : Y ⟶ X) (K E : ModuleDerived X) :
    (K ⟶ E) →+
      ((modulePullbackDerived f).obj K ⟶ (modulePullbackDerived f).obj E) :=
  AddMonoidHom.mk' (fun φ ↦ (modulePullbackDerived f).map φ)
    (pullbackMapAddHom_map_add f K E)

/-- `pullbackMapAddHom` evaluates as `(modulePullbackDerived f).map`. -/
theorem pullbackMapAddHom_toFun (f : Y ⟶ X) (K E : ModuleDerived X)
    (φ : K ⟶ E) :
    pullbackMapAddHom f K E φ = (modulePullbackDerived f).map φ :=
  sorry

/-- The restriction arrow
`Hom_{𝒪_X}(K, E) ⟶ Hom_{𝒪_{U_0}}(La_0^* K, La_0^* E)`. -/
def homRestrict (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (K E : AlgebraicSpace.DerivedQCoh X) :
    AddCommGrpCat.of (K.obj ⟶ E.obj) ⟶
      AddCommGrpCat.of
        ((modulePullbackDerived (stageMap a 0)).obj K.obj ⟶
          (modulePullbackDerived (stageMap a 0)).obj E.obj) :=
  AddCommGrpCat.ofHom (pullbackMapAddHom (stageMap a 0) K.obj E.obj)

/-- `homRestrict` is derived pullback of morphisms along `a_0`. -/
theorem homRestrict_eq (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (K E : AlgebraicSpace.DerivedQCoh X) (φ : K.obj ⟶ E.obj) :
    homRestrict a K E φ = (modulePullbackDerived (stageMap a 0)).map φ :=
  sorry

/-- Additivity of the conjugated face action on Hom-groups. -/
theorem homDiffLeg_map_add (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (i : Fin 2) (K E : AlgebraicSpace.DerivedQCoh X)
    (α β :
      (modulePullbackDerived (stageMap a 0)).obj K.obj ⟶
        (modulePullbackDerived (stageMap a 0)).obj E.obj) :
    ((augmentationFace_pullbackIso a i).app K.obj).inv ≫
        (modulePullbackDerived (augmentationFace a i)).map (α + β) ≫
          ((augmentationFace_pullbackIso a i).app E.obj).hom =
      ((augmentationFace_pullbackIso a i).app K.obj).inv ≫
          (modulePullbackDerived (augmentationFace a i)).map α ≫
            ((augmentationFace_pullbackIso a i).app E.obj).hom +
        ((augmentationFace_pullbackIso a i).app K.obj).inv ≫
          (modulePullbackDerived (augmentationFace a i)).map β ≫
            ((augmentationFace_pullbackIso a i).app E.obj).hom :=
  sorry

/-- The `d_i`-leg of the Čech Hom differential, after identifying
`L(d_i)^* La_0^*` with `La_1^*`. -/
def homDiffLeg (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (i : Fin 2) (K E : AlgebraicSpace.DerivedQCoh X) :
    AddCommGrpCat.of
        ((modulePullbackDerived (stageMap a 0)).obj K.obj ⟶
          (modulePullbackDerived (stageMap a 0)).obj E.obj) ⟶
      AddCommGrpCat.of
        ((modulePullbackDerived (stageMap a 1)).obj K.obj ⟶
          (modulePullbackDerived (stageMap a 1)).obj E.obj) :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun φ ↦
        ((augmentationFace_pullbackIso a i).app K.obj).inv ≫
          (modulePullbackDerived (augmentationFace a i)).map φ ≫
            ((augmentationFace_pullbackIso a i).app E.obj).hom)
      (homDiffLeg_map_add a i K E)

/-- `homDiffLeg a i` is conjugation of `L(d_i)^*` by `augmentationFace_pullbackIso`. -/
theorem homDiffLeg_eq (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (i : Fin 2) (K E : AlgebraicSpace.DerivedQCoh X)
    (φ :
      (modulePullbackDerived (stageMap a 0)).obj K.obj ⟶
        (modulePullbackDerived (stageMap a 0)).obj E.obj) :
    homDiffLeg a i K E φ =
      ((augmentationFace_pullbackIso a i).app K.obj).inv ≫
        (modulePullbackDerived (augmentationFace a i)).map φ ≫
          ((augmentationFace_pullbackIso a i).app E.obj).hom :=
  sorry

/-- The Čech differential
`Hom_{𝒪_{U_0}}(La_0^* K, La_0^* E) ⟶ Hom_{𝒪_{U_1}}(La_1^* K, La_1^* E)`,
equal to the conjugated difference `d_0^* - d_1^*`. -/
def homDiff (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (K E : AlgebraicSpace.DerivedQCoh X) :
    AddCommGrpCat.of
        ((modulePullbackDerived (stageMap a 0)).obj K.obj ⟶
          (modulePullbackDerived (stageMap a 0)).obj E.obj) ⟶
      AddCommGrpCat.of
        ((modulePullbackDerived (stageMap a 1)).obj K.obj ⟶
          (modulePullbackDerived (stageMap a 1)).obj E.obj) :=
  homDiffLeg a 0 K E - homDiffLeg a 1 K E

/-- `homDiff` is the difference of the two conjugated face pullbacks. -/
theorem homDiff_eq (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (K E : AlgebraicSpace.DerivedQCoh X)
    (φ :
      (modulePullbackDerived (stageMap a 0)).obj K.obj ⟶
        (modulePullbackDerived (stageMap a 0)).obj E.obj) :
    homDiff a K E φ = homDiffLeg a 0 K E φ - homDiffLeg a 1 K E φ :=
  sorry

/-- The composite of restriction along `a_0` with the Čech Hom differential is
zero. -/
theorem homRestrict_comp_homDiff (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
    (K E : AlgebraicSpace.DerivedQCoh X) :
    homRestrict a K E ≫ homDiff a K E = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
