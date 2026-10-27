/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ProjectionFormula.Finite
public import ReasLib.CategoryTheory.Homology.DoubleComplex.MapTotal

/-! # The unbounded derived projection formula for finite morphisms -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open RingedSite.NativeDerived.CellTensor

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleDerived.ProjectionFormula

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (π : X ⟶ Y) [IsFinite π]
variable {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
  {B : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
variable (φ : (etaleRingedSite Y B).structureSheaf ⟶
  (ringPushforward π).obj (etaleRingedSite X A).structureSheaf)

/-- Tensor product of the left derived object with the derived direct image of the right one. -/
def source : category Y B × category X A ⥤ category Y B :=
  ((𝟭 (category Y B)).prod (pushforward π φ)) ⋙ tensor Y B

/-- Derived direct image of the tensor product with the derived inverse image of the left object. -/
def target : category Y B × category X A ⥤ category Y B :=
  ((pullback π φ).prod (𝟭 (category X A))) ⋙ tensor X A ⋙ pushforward π φ

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- The tensor bicomplex of the cell replacement and the ordinary direct image. -/
private abbrev sourceBicomplex (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A) :=
  (((curriedTensor (SheafOfModules.{u} (etaleRingedSite Y B).structureSheaf)).mapBifunctorHomologicalComplex
    (up ℤ) (up ℤ)).obj ((replacement B).obj K)).obj ((pushforwardComplex π φ).obj M)

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- The tensor bicomplex of the pulled-back cell replacement and the original right complex. -/
private abbrev tensorBicomplex (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A) :=
  (((curriedTensor (SheafOfModules.{u} (etaleRingedSite X A).structureSheaf)).mapBifunctorHomologicalComplex
    (up ℤ) (up ℤ)).obj ((pullbackComplex π φ).obj
      ((replacement B).obj K))).obj M

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- Degreewise direct image of the target tensor bicomplex. -/
private abbrev targetBicomplex (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A) :=
  (@Functor.mapHomologicalComplex _ _ _ _ _ _ _ (pushforwardComplex π φ)
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ (pushforwardComplex π φ)
      (pushforwardComplex_additive π φ)) (up ℤ)).obj (tensorBicomplex π φ K M)

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- The ordinary canonical projection formula in each bidegree. -/
private def component (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A) (p q : ℤ) :
    ((sourceBicomplex π φ K M).X p).X q ⟶ ((targetBicomplex π φ K M).X p).X q :=
  AlgebraicGeometry.AlgebraicSpace.projectionFormula π φ
    (((replacement B).obj K).X p) (M.X q)

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- The bidegree projection comparison commutes with the first differential. -/
private theorem componentComm₁ (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A)
    (p p' q : ℤ) (h : (up ℤ).Rel p p') :
    component π φ K M p q ≫ ((targetBicomplex π φ K M).d p p').f q =
      ((sourceBicomplex π φ K M).d p p').f q ≫ component π φ K M p' q := sorry

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- The bidegree projection comparison commutes with the second differential. -/
private theorem componentComm₂ (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A)
    (p q q' : ℤ) (h : (up ℤ).Rel q q') :
    component π φ K M p q ≫ ((targetBicomplex π φ K M).X p).d q q' =
      ((sourceBicomplex π φ K M).X p).d q q' ≫ component π φ K M p q' := sorry

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- The specified ordinary comparisons form a map on each column. -/
private def column (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A) (p : ℤ) :
    (sourceBicomplex π φ K M).X p ⟶ (targetBicomplex π φ K M).X p where
  f := component π φ K M p
  comm' := componentComm₂ π φ K M p

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- The specified column maps form the canonical map of tensor bicomplexes. -/
private def bicomplexMap (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A) :
    sourceBicomplex π φ K M ⟶ targetBicomplex π φ K M where
  f := column π φ K M
  comm' := fun p p' h ↦ HomologicalComplex.Hom.ext
    (funext (fun q ↦ componentComm₁ π φ K M p p' q h))

/-- Total tensor of the cell replacement with ordinary direct image. -/
def sourceComplex :
    Complex (J := smallEtaleTopology Y) B × Complex (J := smallEtaleTopology X) A ⥤
      Complex (J := smallEtaleTopology Y) B :=
  ((replacement B).prod (pushforwardComplex π φ)) ⋙
    Functor.uncurry.obj ((curriedTensor (SheafOfModules.{u}
      (etaleRingedSite Y B).structureSheaf)).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)) ⋙
    HomologicalComplex₂.totalFunctor _ (up ℤ) (up ℤ) (up ℤ)

/-- Ordinary direct image of total tensor with the pulled-back cell replacement. -/
def targetComplex :
    Complex (J := smallEtaleTopology Y) B × Complex (J := smallEtaleTopology X) A ⥤
      Complex (J := smallEtaleTopology Y) B :=
  (((replacement B) ⋙ (pullbackComplex π φ)).prod
      (𝟭 (Complex (J := smallEtaleTopology X) A))) ⋙
    Functor.uncurry.obj ((curriedTensor (SheafOfModules.{u}
      (etaleRingedSite X A).structureSheaf)).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)) ⋙
    HomologicalComplex₂.totalFunctor _ (up ℤ) (up ℤ) (up ℤ) ⋙ pushforwardComplex π φ

-- Local declaration justification (metaprogramming implementation): the exposed construction
-- uses private component maps and their Prop-valued compatibility laws under module visibility.
set_option backward.privateInPublic true in
set_option maxHeartbeats 800000 in
/-- Totalization of the ordinary projection comparisons, followed by the direct-image total comparison. -/
def cochainMap (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A) :
    (sourceComplex π φ).obj (K, M) ⟶ (targetComplex π φ).obj (K, M) :=
  HomologicalComplex₂.total.map (bicomplexMap π φ K M) (up ℤ) ≫
    @HomologicalComplex₂.Total.Map.Comparison.hom _ _ _ _ _ _
      (toRingedToposHom π φ).modulePushforward
      (RingedSite.ToposHom.modulePushforward_additive (toRingedToposHom π φ))
      _ _ _ _ _ (tensorBicomplex π φ K M) (up ℤ) _ _ _ _

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- The totalized ordinary projection comparison is natural in both original complexes. -/
private theorem cochainNaturality {P P' : Complex (J := smallEtaleTopology Y) B ×
      Complex (J := smallEtaleTopology X) A} (a : P ⟶ P') :
    (sourceComplex π φ).map a ≫ cochainMap π φ P'.1 P'.2 =
      cochainMap π φ P.1 P.2 ≫ (targetComplex π φ).map a := sorry

-- Local declaration justification (metaprogramming implementation): the exposed construction
-- uses private component maps and their Prop-valued compatibility laws under module visibility.
set_option backward.privateInPublic true in
/-- The canonical totalized projection comparison as a natural transformation of complex models. -/
def cochainComparison : sourceComplex π φ ⟶ targetComplex π φ where
  app P := cochainMap π φ P.1 P.2
  naturality := fun _ _ a ↦ cochainNaturality π φ a

/-- Derived tensor and exact direct image computed on the displayed source complex. -/
def sourceComputationApp (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A) :
    (source π φ).obj ((Q B).obj K, (Q A).obj M) ≅
      (Q B).obj ((sourceComplex π φ).obj (K, M)) :=
  (tensor Y B).mapIso ((Iso.refl ((Q B).obj K)).prod ((pushforwardComputation π φ).app M)) ≪≫
    (computation B).app (K, (pushforwardComplex π φ).obj M) ≪≫
    Localization.formalIso (quasiIso B) (Q B)
      (HomologicalComplex.tensorHom (𝟙 ((replacement B).obj K))
        ((augmentation B).app ((pushforwardComplex π φ).obj M)))
      (augmentationRight_quasiIso B ((replacement B).obj K)
        ((pushforwardComplex π φ).obj M)
        (SheafOfModules.RingedSite.CellReplacement.model_isKFlat K))

-- The three computation isomorphisms require unfolding nested tensor totalizations.
set_option maxHeartbeats 800000 in
/-- Derived inverse image, tensor, and exact direct image computed on the displayed target complex. -/
def targetComputationApp (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A) :
    (target π φ).obj ((Q B).obj K, (Q A).obj M) ≅
      (Q B).obj ((targetComplex π φ).obj (K, M)) :=
  let P := (pullbackComplex π φ).obj ((replacement B).obj K)
  let hP := @RingedSite.ToposHom.modulePullbackComplex.isKFlat_of_isTermwiseFlat
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B (toRingedToposHom π φ)
    (restrictScalars_toRingedToposHom_isRightAdjoint π φ) ((replacement B).obj K)
    (SheafOfModules.RingedSite.CellReplacement.model_isKFlat K)
    (SheafOfModules.RingedSite.CellReplacement.model_termwiseFlat K)
  (pushforward π φ).mapIso
    ((tensor X A).mapIso
        (((@RingedSite.ToposHom.NativeDerived.CellPullback.computation
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B (toRingedToposHom π φ)
          (restrictScalars_toRingedToposHom_isRightAdjoint π φ)).app K).prod (Iso.refl ((Q A).obj M))) ≪≫
      (computation A).app (P, M) ≪≫
      Localization.formalIso (quasiIso A) (Q A)
        (HomologicalComplex.tensorHom ((augmentation A).app P) (𝟙 ((replacement A).obj M)))
        (augmentationLeft_quasiIso A P ((replacement A).obj M)
          (SheafOfModules.RingedSite.CellReplacement.model_isKFlat M)) ≪≫
      Localization.formalIso (quasiIso A) (Q A)
        (HomologicalComplex.tensorHom (𝟙 P) ((augmentation A).app M))
        (augmentationRight_quasiIso A P M hP)) ≪≫
    (pushforwardComputation π φ).app (HomologicalComplex.tensorObj P M)

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- The specified source computation is natural in the two original complexes. -/
private theorem sourceComputationNaturality {P P' : Complex (J := smallEtaleTopology Y) B ×
      Complex (J := smallEtaleTopology X) A} (a : P ⟶ P') :
    (((Q B).prod (Q A)) ⋙ source π φ).map a ≫
        (sourceComputationApp π φ P'.1 P'.2).hom =
      (sourceComputationApp π φ P.1 P.2).hom ≫
        (sourceComplex π φ ⋙ Q B).map a := sorry

-- Local declaration justification (metaprogramming implementation): retain a private name
-- while exporting this component for the exposed totalized construction.
set_option backward.privateInPublic true in
/-- The specified target computation is natural in the two original complexes. -/
private theorem targetComputationNaturality {P P' : Complex (J := smallEtaleTopology Y) B ×
      Complex (J := smallEtaleTopology X) A} (a : P ⟶ P') :
    (((Q B).prod (Q A)) ⋙ target π φ).map a ≫
        (targetComputationApp π φ P'.1 P'.2).hom =
      (targetComputationApp π φ P.1 P.2).hom ≫
        (targetComplex π φ ⋙ Q B).map a := sorry

-- Local declaration justification (metaprogramming implementation): the exposed construction
-- uses private component maps and their Prop-valued compatibility laws under module visibility.
set_option backward.privateInPublic true in
/-- The source-side computation isomorphism on the original complex models. -/
def sourceComputation : ((Q B).prod (Q A)) ⋙ source π φ ≅ sourceComplex π φ ⋙ Q B :=
  NatIso.ofComponents (fun P ↦ sourceComputationApp π φ P.1 P.2)
    (fun a ↦ sourceComputationNaturality π φ a)

-- Local declaration justification (metaprogramming implementation): the exposed construction
-- uses private component maps and their Prop-valued compatibility laws under module visibility.
set_option backward.privateInPublic true in
/-- The target-side computation isomorphism on the original complex models. -/
def targetComputation : ((Q B).prod (Q A)) ⋙ target π φ ≅ targetComplex π φ ⋙ Q B :=
  NatIso.ofComponents (fun P ↦ targetComputationApp π φ P.1 P.2)
    (fun a ↦ targetComputationNaturality π φ a)

end AlgebraicGeometry.AlgebraicSpace.EtaleDerived.ProjectionFormula

namespace AlgebraicGeometry.AlgebraicSpace.EtaleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (π : X ⟶ Y) [IsFinite π]
variable {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
  {B : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
variable (φ : (etaleRingedSite Y B).structureSheaf ⟶
  (ringPushforward π).obj (etaleRingedSite X A).structureSheaf)

/-- The derived projection formula obtained by descending the totalized ordinary comparison. -/
def projectionFormula (K : category Y B) (M : category X A) :
    (tensor Y B).obj (K, (pushforward π φ).obj M) ⟶
      (pushforward π φ).obj ((tensor X A).obj ((pullback π φ).obj K, M)) :=
  (Localization.liftNatTrans ((Q B).prod (Q A)) ((quasiIso B).prod (quasiIso A))
    (((Q B).prod (Q A)) ⋙ ProjectionFormula.source π φ)
    (((Q B).prod (Q A)) ⋙ ProjectionFormula.target π φ)
    (ProjectionFormula.source π φ) (ProjectionFormula.target π φ)
    ((ProjectionFormula.sourceComputation π φ).hom ≫
      Functor.whiskerRight (ProjectionFormula.cochainComparison π φ) (Q B) ≫
      (ProjectionFormula.targetComputation π φ).inv)).app (K, M)

/-- On complex models the derived comparison is the totalization of the ordinary projection map. -/
theorem ProjectionFormula.onModels (K : Complex (J := smallEtaleTopology Y) B)
    (M : Complex (J := smallEtaleTopology X) A) :
    projectionFormula π φ ((Q B).obj K) ((Q A).obj M) ≫
        (targetComputationApp π φ K M).hom =
      (sourceComputationApp π φ K M).hom ≫ (Q B).map (cochainMap π φ K M) := sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleDerived

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical projection-formula morphism is invertible for a finite morphism and all
unbounded derived objects over arbitrary commutative étale coefficient sheaves. -/
@[instance]
theorem IsFinite.derivedProjectionFormula
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (π : X ⟶ Y) [IsFinite π]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (B : Sheaf (smallEtaleTopology Y) CommRingCat.{u})
    (φ : (etaleRingedSite Y B).structureSheaf ⟶
      (ringPushforward π).obj (etaleRingedSite X A).structureSheaf)
    (K : EtaleDerived.category Y B) (M : EtaleDerived.category X A) :
    IsIso (EtaleDerived.projectionFormula π φ K M) := sorry

end AlgebraicGeometry.AlgebraicSpace
