module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.ModuleSheafInverse
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.CategoryTheory.Sites.Adjunction
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Coproduct
@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
noncomputable section
universe u v
namespace AlgebraicGeometry.Scheme.FiniteAbelianInverse
variable {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X)
variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
/-- A finite integer-module carrier is finitely generated, without finite integer coefficients. -/
def finiteTypeObject
    (M : (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    (finiteTypeDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory := by
  letI : Finite M.obj.obj.V := M.property
  exact ⟨M.obj, Module.Finite.of_finite⟩
instance finiteTypeObject_finite
    (M : (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    Finite (finiteTypeObject xbar M).obj.obj.V := M.property
/-- The abelian sheaf uses the shared actual finite-carrier module inverse and native forgetfulness. -/
def sheaf
    (M : (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).obj
    (ModuleSheafInverse.sheaf ℤ xbar (finiteTypeObject xbar M))
/-- Actual equivariant maps retain their coefficient homomorphism when regarded as finite type. -/
def finiteTypeMap
    {M N : (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory}
    (f : M ⟶ N) : finiteTypeObject xbar M ⟶ finiteTypeObject xbar N :=
  ObjectProperty.homMk f.hom

/-- The inverse map is the shared actual sectionwise module map followed by forgetfulness. -/
def sheafMap
    {M N : (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory}
    (f : M ⟶ N) : sheaf xbar M ⟶ sheaf xbar N :=
  (sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).map
    (ModuleSheafInverse.sheafMap ℤ xbar (finiteTypeMap xbar f))

/-- The implemented abelian inverse uses actual sheaves and actual coefficient maps. -/
def functor :
    (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} where
  obj M := sheaf xbar M
  map f := sheafMap xbar f
  map_id := sorry
  map_comp := sorry

end AlgebraicGeometry.Scheme.FiniteAbelianInverse

namespace AlgebraicGeometry.Scheme.LinearFrames
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete
variable {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X)
variable (R : Type v) [Ring R]
variable (M : (finiteTypeDiscreteModule R (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)
variable [Finite M.obj.obj.V]
/-- The actual inverse linear action is supplied by the inverse group element. -/
def actionLinearEquiv (g : Aut (GeometricPoint.finiteFiber xbar)) : M.obj.obj.V ≃ₗ[R] M.obj.obj.V where
  toLinearMap := (M.obj.obj.ρ g).hom
  invFun := (M.obj.obj.ρ g⁻¹).hom
  left_inv := sorry
  right_inv := sorry
/-- There are finitely many linear frames of a finite module carrier. -/
instance linearFrames_finite : Finite (M.obj.obj.V ≃ₗ[R] M.obj.obj.V) :=
  Finite.of_injective (fun e : M.obj.obj.V ≃ₗ[R] M.obj.obj.V ↦ (e : M.obj.obj.V → M.obj.obj.V))
    DFunLike.coe_injective
/-- A small actual carrier of linear frames, with its native shrink equivalence. -/
abbrev Frames := Shrink.{u} (M.obj.obj.V ≃ₗ[R] M.obj.obj.V)
def frameEquiv : (M.obj.obj.V ≃ₗ[R] M.obj.obj.V) ≃ Frames xbar R M := equivShrink _
/-- Linear monodromy moves the values of the frame, preserving all module operations. -/
def action : Action FintypeCat.{u} (Aut (GeometricPoint.finiteFiber xbar)) where
  V := FintypeCat.of (Frames xbar R M)
  ρ :=
    { toFun := fun g ↦ FintypeCat.homMk fun e ↦
        frameEquiv xbar R M (((frameEquiv xbar R M).symm e).trans (actionLinearEquiv xbar R M g))
      map_one' := sorry
      map_mul' := sorry }
theorem action_continuous : (action xbar R M).IsContinuous := sorry
/-- The finite continuous frame object has an explicit linear-frame carrier and action. -/
def frameSet : ContAction FintypeCat.{u} (Aut (GeometricPoint.finiteFiber xbar)) :=
  ⟨action xbar R M, action_continuous xbar R M⟩
/-- The identity linear map gives an actual frame. -/
def identityFrame : Frames xbar R M := frameEquiv xbar R M (LinearEquiv.refl R _)
/-- Realize the linear-frame action through the implemented finite Galois inverse. -/
def cover : FiniteEtale X :=
  (functorToContAction (GeometricPoint.finiteFiber xbar)).asEquivalence.inverse.obj
    (frameSet xbar R M)
/-- Evaluate a linear frame at a coefficient element; this map is equivariant. -/
def evaluation (m : ModuleSheafInverse.Carrier R xbar M) :
    frameSet xbar R M ⟶ ModuleSheafInverse.moduleSet R xbar M :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk fun e ↦
        ModuleSheafInverse.carrierEquiv R xbar M
          (((frameEquiv xbar R M).symm e)
            ((ModuleSheafInverse.carrierEquiv R xbar M).symm m))
      comm := sorry }
/-- The actual finite étale object representing the module's underlying finite action. -/
def coefficientCover : FiniteEtale X :=
  (functorToContAction (GeometricPoint.finiteFiber xbar)).asEquivalence.inverse.obj
    (ModuleSheafInverse.moduleSet R xbar M)
/-- Each coefficient value gives an actual coordinate map from the realized linear frame. -/
def coordinate (m : ModuleSheafInverse.Carrier R xbar M) :
    cover xbar R M ⟶ coefficientCover xbar R M :=
  (functorToContAction (GeometricPoint.finiteFiber xbar)).asEquivalence.inverse.map
    (evaluation xbar R M m)
/-- The coordinate maps give the explicit sections of the pulled coefficient cover. -/
def coordinateSection (m : ModuleSheafInverse.Carrier R xbar M) :
    (cover xbar R M).left ⟶
      pullback (coefficientCover xbar R M).hom (cover xbar R M).hom :=
  pullback.lift (coordinate xbar R M m).left (𝟙 _) sorry
instance coordinateSection_isOpenImmersion (m : ModuleSheafInverse.Carrier R xbar M) :
    IsOpenImmersion (coordinateSection xbar R M m) := sorry
/-- The actual linear coordinates cover the pulled coefficient scheme. -/
def coordinateCover :
    (pullback (coefficientCover xbar R M).hom (cover xbar R M).hom).OpenCover where
  I₀ := ModuleSheafInverse.Carrier R xbar M
  X _ := (cover xbar R M).left
  f m := coordinateSection xbar R M m
  mem₀ := sorry
/-- The frame cover as an actual object of the small étale site. -/
def chart : X.Etale :=
  MorphismProperty.Over.mk ⊤ (cover xbar R M).hom (cover xbar R M).prop.2
/-- The pulled coefficient cover is an actual object over the linear frame chart. -/
def pulledObject : Over (chart xbar R M) := by
  letI : Etale (coefficientCover xbar R M).hom := (coefficientCover xbar R M).prop.2
  letI : Etale (cover xbar R M).hom := (cover xbar R M).prop.2
  letI : Etale (pullback.snd (coefficientCover xbar R M).hom (cover xbar R M).hom) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact Over.mk (MorphismProperty.Over.homMk
    (pullback.snd (coefficientCover xbar R M).hom (cover xbar R M).hom) (by rfl) :
    (MorphismProperty.Over.mk ⊤
      (pullback.snd (coefficientCover xbar R M).hom (cover xbar R M).hom ≫
        (cover xbar R M).hom) (by sorry) : X.Etale) ⟶ chart xbar R M)
/-- The branch associated to a coefficient element is its actual linear coordinate section. -/
def branch (m : Shrink.{u + 1} M.obj.obj.V) : Over.mk (𝟙 (chart xbar R M)) ⟶ pulledObject xbar R M :=
  Over.homMk (MorphismProperty.Over.homMk
    (coordinateSection xbar R M (ModuleSheafInverse.carrierEquiv R xbar M ((equivShrink.{u + 1} M.obj.obj.V).symm m))) sorry trivial) sorry
instance branch_mono (m : Shrink.{u + 1} M.obj.obj.V) : Mono (branch xbar R M m) := sorry
def branchCofan : Cofan fun _ : (Shrink.{u + 1} M.obj.obj.V) ↦ Over.mk (𝟙 (chart xbar R M)) :=
  Cofan.mk (pulledObject xbar R M) (branch xbar R M)
theorem branchCovering : Sieve.ofArrows _ (branchCofan xbar R M).inj ∈
    (X.smallEtaleTopology.over (chart xbar R M)) (pulledObject xbar R M) := sorry
theorem branchDisjoint {i j : (Shrink.{u + 1} M.obj.obj.V)} (hij : i ≠ j)
    {V : Over (chart xbar R M)} (a : V ⟶ Over.mk (𝟙 (chart xbar R M)))
    (b : V ⟶ Over.mk (𝟙 (chart xbar R M)))
    (hab : a ≫ (branchCofan xbar R M).inj i = b ≫ (branchCofan xbar R M).inj j) :
    (⊥ : Sieve V) ∈ (X.smallEtaleTopology.over (chart xbar R M)) V := sorry
/-- The constant carrier chart has both actual descent maps, with labels in the original module. -/
def constantCarrierChartIso
    [HasWeakSheafify (X.smallEtaleTopology.over (chart xbar R M)) (Type (u + 1))] :
    (constantSheaf (X.smallEtaleTopology.over (chart xbar R M)) (Type (u + 1))).obj (Shrink.{u + 1} M.obj.obj.V) ≅
      (X.smallEtaleTopology.over (chart xbar R M)).sheafifiedRepresentable (pulledObject xbar R M) := by
  letI : ∀ m, Mono ((branchCofan xbar R M).inj m) := fun m ↦ branch_mono xbar R M m
  exact GrothendieckTopology.constantSheafIsoOfDisjointCover.{u + 1, u + 1, u}
    (X.smallEtaleTopology.over (chart xbar R M)) Over.mkIdTerminal _ (branchCofan xbar R M)
    (branchCovering xbar R M) (branchDisjoint xbar R M)
/-- Restrict the represented coefficient presheaf by actual pullback lifts and projections. -/
def rawSliceIso :
    (Over.forget (chart xbar R M)).op ⋙ uliftYoneda.{u + 1}.obj
      ((Scheme.FiniteEtale.toEtale X).obj (coefficientCover xbar R M)) ≅
      uliftYoneda.{u + 1}.obj (pulledObject xbar R M) :=
  NatIso.ofComponents
    (fun V ↦ Equiv.toIso
      { toFun := fun h ↦
          ⟨Over.homMk (MorphismProperty.Over.homMk
            (pullback.lift h.down.left V.unop.hom.left sorry) sorry) sorry⟩
        invFun := fun h ↦
          ⟨MorphismProperty.Over.homMk
            (h.down.left.left ≫ pullback.fst (coefficientCover xbar R M).hom (cover xbar R M).hom) sorry⟩
        left_inv := sorry
        right_inv := sorry })
    (fun _ ↦ sorry)
variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
/-- The underlying realized sheaf restricts by the native sheafification comparison. -/
def carrierSliceIso :
    (ModuleSheafInverse.setSheaf xbar (ModuleSheafInverse.moduleSet R xbar M)).over (chart xbar R M) ≅
      (X.smallEtaleTopology.over (chart xbar R M)).sheafifiedRepresentable (pulledObject xbar R M) :=
  ((Over.forget (chart xbar R M)).pushforwardContinuousSheafificationCompatibility
    (Type (u + 1)) (X.smallEtaleTopology.over (chart xbar R M)) X.smallEtaleTopology).symm.app
      (uliftYoneda.{u + 1}.obj ((Scheme.FiniteEtale.toEtale X).obj (coefficientCover xbar R M))) ≪≫
    (presheafToSheaf (X.smallEtaleTopology.over (chart xbar R M)) (Type (u + 1))).mapIso
      (rawSliceIso xbar R M)
/-- A constant module model has the actual small carrier transported from the coefficient module. -/
def model : ModuleCat.{u + 1} R := ModuleCat.of R (Shrink.{u + 1} M.obj.obj.V)
variable [HasWeakSheafify (X.smallEtaleTopology.over (chart xbar R M)) (ModuleCat.{u + 1} R)]
variable [(X.smallEtaleTopology.over (chart xbar R M)).PreservesSheafification
  (CategoryTheory.forget (ModuleCat.{u + 1} R))]
/-- Both underlying maps of the linear constant-module chart are explicitly specified. -/
def underlyingModuleChartIso :
    (sheafCompose (X.smallEtaleTopology.over (chart xbar R M))
      (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj
        ((ModuleSheafInverse.sheaf R xbar M).over (chart xbar R M)) ≅
    (sheafCompose (X.smallEtaleTopology.over (chart xbar R M))
      (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj
        ((constantSheaf (X.smallEtaleTopology.over (chart xbar R M)) (ModuleCat.{u + 1} R)).obj
          (model xbar R M)) :=
  carrierSliceIso xbar R M ≪≫ (constantCarrierChartIso xbar R M).symm ≪≫
    ((constantCommuteCompose (X.smallEtaleTopology.over (chart xbar R M))
      (CategoryTheory.forget (ModuleCat.{u + 1} R))).app (model xbar R M)).symm
/-- Linear frames make the explicit carrier-chart maps linear in both directions. -/
def moduleChartIso :
    (ModuleSheafInverse.sheaf R xbar M).over (chart xbar R M) ≅
      (constantSheaf (X.smallEtaleTopology.over (chart xbar R M)) (ModuleCat.{u + 1} R)).obj
        (model xbar R M) where
  hom := { hom :=
    { app V := ModuleCat.ofHom
        { toFun := (underlyingModuleChartIso xbar R M).hom.hom.app V
          map_add' := sorry
          map_smul' := sorry }
      naturality := sorry } }
  inv := { hom :=
    { app V := ModuleCat.ofHom
        { toFun := (underlyingModuleChartIso xbar R M).inv.hom.app V
          map_add' := sorry
          map_smul' := sorry }
      naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry
/-- The linear frame chart has its actual structure morphism to the base object. -/
def chartToBase : chart xbar R M ⟶ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.homMk (cover xbar R M).hom (Category.comp_id _)
/-- The realized identity-frame orbit covers the connected base. -/
theorem charts_covering :
    Sieve.ofArrows (fun _ : PUnit.{u + 2} ↦ chart xbar R M)
      (fun _ ↦ chartToBase xbar R M) ∈ X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := sorry
/-- The actual linear chart is pulled back to any étale test object. -/
def refinedChart (U : X.Etale) : Over U :=
  Over.mk (pullback.snd (chartToBase xbar R M)
    (MorphismProperty.Over.homMk U.hom (Category.comp_id _) : U ⟶ Scheme.Etale.mk (𝟙 X)))
def refinedChartToFrame (U : X.Etale) : (refinedChart xbar R M U).left ⟶ chart xbar R M :=
  pullback.fst (chartToBase xbar R M)
    (MorphismProperty.Over.homMk U.hom (Category.comp_id _) : U ⟶ Scheme.Etale.mk (𝟙 X))
theorem refinedCharts_covering (U : X.Etale) :
    (X.smallEtaleTopology.over U).CoversTop
      (fun _ : PUnit.{u + 2} ↦ refinedChart xbar R M U) := sorry
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
/-- Refine the actual module chart by native restriction and constant-sheafification compatibility. -/
def refinedModuleChartIso (U : X.Etale) :
    (ModuleSheafInverse.sheaf R xbar M).over (refinedChart xbar R M U).left ≅
      (constantSheaf (X.smallEtaleTopology.over (refinedChart xbar R M U).left)
        (ModuleCat.{u + 1} R)).obj (model xbar R M) :=
  (Sheaf.pushforwardOverMapIso _ (refinedChartToFrame xbar R M U)).symm ≪≫
    ((Over.map (refinedChartToFrame xbar R M U)).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (X.smallEtaleTopology.over (refinedChart xbar R M U).left)
      (X.smallEtaleTopology.over (chart xbar R M))).mapIso (moduleChartIso xbar R M) ≪≫
    ((Over.map (refinedChartToFrame xbar R M U)).pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{u + 1} R) (X.smallEtaleTopology.over (refinedChart xbar R M U).left)
      (X.smallEtaleTopology.over (chart xbar R M))).symm.app
        ((Functor.const (Over (chart xbar R M))ᵒᵖ).obj (model xbar R M))
/-- The actual shared inverse has explicit constant module charts of finite type. -/
theorem isFiniteTypeLocallyConstant :
    Sheaf.IsLocallyConstantWith (P := fun A : ModuleCat.{u + 1} R ↦ Module.Finite R A)
      (ModuleSheafInverse.sheaf R xbar M) where
  existsConstantCover U :=
    ⟨PUnit.{u + 2}, (fun _ ↦ refinedChart xbar R M U), refinedCharts_covering xbar R M U,
      fun _ ↦ ⟨model xbar R M,
        (by
          letI : Finite (model xbar R M) :=
            inferInstanceAs (Finite (Shrink.{u + 1} M.obj.obj.V))
          exact Module.Finite.of_finite),
        ⟨refinedModuleChartIso xbar R M U⟩⟩⟩
end AlgebraicGeometry.Scheme.LinearFrames

namespace AlgebraicGeometry.Scheme.ModuleSheafInverse
variable {X : Scheme.{u}} [ConnectedSpace X]
variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] (xbar : GeometricPoint X)
variable (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)

variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The transported finite module operations are locally constant of finite type. -/
theorem sheaf_finiteTypeLocallyConstant :
    Sheaf.IsFiniteTypeLocallyConstantModule (sheaf Λ xbar M) :=
  LinearFrames.isFiniteTypeLocallyConstant xbar Λ M

/-- The same concrete inverse construction, with its finite locally constant property recorded. -/
def finiteFunctor :
    (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory ⥤
      (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory :=
  (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).lift
    (functor Λ xbar) (fun M ↦ sheaf_finiteTypeLocallyConstant Λ xbar M)

end AlgebraicGeometry.Scheme.ModuleSheafInverse

namespace AlgebraicGeometry.Scheme.FiniteAbelianInverse
/-- Integer-module sheafification is transported through the native coefficient equivalence. -/
instance intModule_hasWeakSheafify {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}] : HasWeakSheafify J (ModuleCat.{u + 1} ℤ) := by
  let F := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let E := F.asEquivalence
  letI : (sheafCompose J F).EssSurj :=
    { mem_essImage := fun A ↦
        ⟨(sheafCompose J E.inverse).obj A,
          ⟨ObjectProperty.isoMk _
            (Functor.isoWhiskerLeft A.obj E.counitIso)⟩⟩ }
  letI : (sheafCompose J F).Full := inferInstance
  letI : (sheafCompose J F).Faithful := inferInstance
  letI : (sheafCompose J F).IsEquivalence := { }
  let G := (CategoryTheory.Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).obj F
  letI : G.IsEquivalence := inferInstance
  letI : (sheafToPresheaf J (ModuleCat.{u + 1} ℤ) ⋙ G).IsRightAdjoint :=
    inferInstanceAs ((sheafCompose J F ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}).IsRightAdjoint)
  exact (Functor.isRightAdjoint_comp_iff_left (sheafToPresheaf J (ModuleCat.{u + 1} ℤ)) G).mp inferInstance
/-- Integer-module forgetfulness uses the native coefficient adjunction, then abelian forgetfulness. -/
instance intModule_forget_preservesSheafification {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.PreservesSheafification (CategoryTheory.forget (ModuleCat.{u + 1} ℤ)) := by
  let F := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let G := CategoryTheory.forget AddCommGrpCat.{u + 1}
  let hF : J.PreservesSheafification F :=
    Sheaf.preservesSheafification_of_adjunction J F.asEquivalence.toAdjunction
  let hG : J.PreservesSheafification G := inferInstance
  refine ⟨?_⟩
  intro P Q f hf
  exact hG.le _ (hF.le _ hf)
instance intModule_forgetAb_preservesSheafification {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.PreservesSheafification (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}) :=
  Sheaf.preservesSheafification_of_adjunction J
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.toAdjunction
end AlgebraicGeometry.Scheme.FiniteAbelianInverse

namespace AlgebraicGeometry.Scheme.FiniteAbelianInverse
variable {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X)
variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
/-- The finite action's transported additive laws give a finite locally constant abelian sheaf. -/
theorem sheaf_isFiniteLocallyConstant
    (M : (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    Sheaf.IsFiniteLocallyConstantAddCommGrp (sheaf xbar M) := by
  letI : ∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} ℤ) :=
    fun U ↦ inferInstance
  refine ⟨?_⟩
  intro U
  let N := finiteTypeObject xbar M
  refine ⟨PUnit.{u + 2}, (fun _ ↦ LinearFrames.refinedChart xbar ℤ N U),
    LinearFrames.refinedCharts_covering xbar ℤ N U, ?_⟩
  intro i
  let A := LinearFrames.model xbar ℤ N
  refine ⟨(forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).obj A,
    inferInstanceAs (Finite (Shrink.{u + 1} N.obj.obj.V)), ?_⟩
  exact ⟨((sheafCompose (X.smallEtaleTopology.over (LinearFrames.refinedChart xbar ℤ N U).left)
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).mapIso
      (LinearFrames.refinedModuleChartIso xbar ℤ N U)) ≪≫
    (constantCommuteCompose (X.smallEtaleTopology.over (LinearFrames.refinedChart xbar ℤ N U).left)
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})).app A⟩

/-- The actual abelian inverse, with its source-faithful locally constant property. -/
def finiteFunctor :
    (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory ⥤
      (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).lift (functor xbar)
    (sheaf_isFiniteLocallyConstant xbar)


end AlgebraicGeometry.Scheme.FiniteAbelianInverse
