module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom.Bifunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Complex
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact

/-! # Exact pullback and derived sheaf internal Hom -/

public section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite SheafOfModules.RingedSite.RingedSiteDerived

noncomputable section

universe u v

namespace SheafOfModules.Pullback.DerivedInternalHom

open RingedSite.Hom.ModuleDerived.InternalHom

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [K.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (G : C ⥤ D) [G.IsContinuous J K] [RepresentablyFlat G]
variable {O : Sheaf J CommRingCat.{max u v}} {O' : Sheaf K CommRingCat.{max u v}}
variable (b : O ⟶ (G.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O')
variable [(PresheafOfModules.pushforward.{max u v} (ringMap G b).hom).IsRightAdjoint]

private def degreeComparison
    (A I : CochainComplex (ringedSiteModuleCategory J O) ℤ) (n : ℤ) :
    (SheafOfModules.pullback.{max u v} (ringMap G b)).obj (((strictInternalHom.obj (op A)).obj I).X n) ⟶
      ((strictInternalHom.obj (op (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj A))).obj
        (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj I)).X n :=
  Pi.lift fun i ↦
    (SheafOfModules.pullback.{max u v} (ringMap G b)).map (Pi.π (fun i ↦ (ihom (A.X i)).obj (I.X (i + n))) i) ≫
      Functor.LaxMonoidal.InternalHom.comparison (SheafOfModules.pullback.{max u v} (ringMap G b)) (A.X i) (I.X (i + n))

/-- The degreewise pullback comparison commutes with the internal-Hom differentials. -/
theorem complexComparison_comm
    (A I : CochainComplex (ringedSiteModuleCategory J O) ℤ) (n m : ℤ) :
    (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj
          ((strictInternalHom.obj (op A)).obj I)).d n m ≫
        (Pi.lift fun i ↦
          (SheafOfModules.pullback.{max u v} (ringMap G b)).map
            (Pi.π (fun i ↦ (ihom (A.X i)).obj (I.X (i + m))) i) ≫
          Functor.LaxMonoidal.InternalHom.comparison
            (SheafOfModules.pullback.{max u v} (ringMap G b)) (A.X i) (I.X (i + m))) =
      (Pi.lift fun i ↦
        (SheafOfModules.pullback.{max u v} (ringMap G b)).map
          (Pi.π (fun i ↦ (ihom (A.X i)).obj (I.X (i + n))) i) ≫
        Functor.LaxMonoidal.InternalHom.comparison
          (SheafOfModules.pullback.{max u v} (ringMap G b)) (A.X i) (I.X (i + n))) ≫
        (((strictInternalHom.obj
          (op (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj A))).obj
            (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj I)).d n m) := by
  sorry

/-- Pullback of a sheaf internal-Hom complex maps to the internal Hom of the pulled-back
complexes by the product of the ordinary pullback comparisons. -/
def complexComparison (A I : CochainComplex (ringedSiteModuleCategory J O) ℤ) :
    ((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj
        ((strictInternalHom.obj (op A)).obj I) ⟶
      (strictInternalHom.obj (op (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj A))).obj
        (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj I) where
  f := degreeComparison G b A I
  comm' n m _ := (complexComparison_comm G b A I n m).symm

/-- Each product projection of the complex comparison is ordinary pullback followed by the
module-sheaf internal-Hom comparison. -/
@[reassoc]
theorem complexComparison_f
    (A I : CochainComplex (ringedSiteModuleCategory J O) ℤ) (n i : ℤ) :
    (complexComparison G b A I).f n ≫
        Pi.π (fun j ↦ (ihom ((SheafOfModules.pullback.{max u v} (ringMap G b)).obj (A.X j))).obj
          ((SheafOfModules.pullback.{max u v} (ringMap G b)).obj (I.X (j + n)))) i =
      (SheafOfModules.pullback.{max u v} (ringMap G b)).map (Pi.π (fun j ↦ (ihom (A.X j)).obj (I.X (j + n))) i) ≫
        Functor.LaxMonoidal.InternalHom.comparison (SheafOfModules.pullback.{max u v} (ringMap G b)) (A.X i) (I.X (i + n)) := by
  exact Pi.lift_π _ i

private theorem strictPre_isIso
    {A B : CochainComplex (ringedSiteModuleCategory K O') ℤ}
    (f : A ⟶ B) (N : max K O') (hf : QuasiIso f) :
    IsIso (DerivedCategory.Q.map
      ((strictInternalHom.map f.op).app (injectiveModel N))) := by
  let tensorExists : ∀ X Y : GradedObject ℤ (ringedSiteModuleCategory K O'),
      GradedObject.HasTensor X Y := fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  let goodLeft : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory K O'),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let goodRight : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory K O'),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let tensorExt : ∀ X Y Z W : GradedObject ℤ (ringedSiteModuleCategory K O'),
      GradedObject.HasTensor₄ObjExt X Y Z W :=
    fun _ _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let preservesLeft : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory K O'))
      ((CategoryTheory.MonoidalCategory.curriedTensor (ringedSiteModuleCategory K O')).obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  let preservesRight : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory K O'))
      ((CategoryTheory.MonoidalCategory.curriedTensor (ringedSiteModuleCategory K O')).flip.obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  let closed := @CochainComplex.InternalHom.monoidalClosed
    (ringedSiteModuleCategory K O')
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance tensorExists goodLeft goodRight tensorExt
    preservesLeft preservesRight
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  have hq := @SheafOfModules.RingedSite.IHom.quasiIso_map
    _ inferInstance K inferInstance inferInstance inferInstance O' _ closed
    _ _ _ _ inferInstance inferInstance f (𝟙 (injectiveModel N)) hf
    (inferInstance : QuasiIso (𝟙 (injectiveModel N)))
  unfold MonoidalClosed.Source.map at hq
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hq
  exact hq

private def strictPreIso
    {A B : CochainComplex (ringedSiteModuleCategory K O') ℤ}
    (f : A ⟶ B) (N : max K O') (hf : QuasiIso f) :
    objOfModels B (injectiveModel N) ≅ objOfModels A (injectiveModel N) :=
  @asIso _ _ _ _ (DerivedCategory.Q.map
    ((strictInternalHom.map f.op).app (injectiveModel N))) (strictPre_isIso f N hf)

private theorem lift_quasiIso
    (A : CochainComplex (ringedSiteModuleCategory K O') ℤ) (N : max K O')
    (e : DerivedCategory.Q.obj A ≅ N) :
    QuasiIso (liftToInjectiveModel A N e.hom) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
  have h : DerivedCategory.Q.map (liftToInjectiveModel A N e.hom) =
      e.hom ≫ (injectiveModelIso N).inv := by
    apply (cancel_mono (injectiveModelIso N).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (liftToInjectiveModel_fac A N e.hom)
  rw [h]
  infer_instance

variable (h : exactFunctor (ringedSiteModuleCategory J O)
  (ringedSiteModuleCategory K O') (SheafOfModules.pullback.{max u v} (ringMap G b)))

private def exactPullback :
    ringedSiteModuleCategory J O ⥤ₑ ringedSiteModuleCategory K O' := ⟨SheafOfModules.pullback.{max u v} (ringMap G b), h⟩

private abbrev derivedPullback : max J O ⥤ max K O' :=
  (exactPullback G b h).mapDerivedCategory

private def pulledModelIso
    {A : CochainComplex (ringedSiteModuleCategory J O) ℤ} {E : max J O}
    (e : DerivedCategory.Q.obj A ≅ E) :
    DerivedCategory.Q.obj (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj A) ≅
      (derivedPullback G b h).obj E :=
  ((exactPullback G b h).obj.mapDerivedCategoryFactors.app A).symm ≪≫
    (derivedPullback G b h).mapIso e

private def pulledModelMap
    {A : CochainComplex (ringedSiteModuleCategory J O) ℤ} {E : max J O}
    (e : DerivedCategory.Q.obj A ≅ E) :
    ((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj A ⟶
      injectiveModel ((derivedPullback G b h).obj E) :=
  liftToInjectiveModel _ _ (pulledModelIso G b h e).hom

private def pulledSourceIso (E F : max J O) :
    objOfModels (injectiveModel ((derivedPullback G b h).obj E))
        (injectiveModel ((derivedPullback G b h).obj F)) ≅
      objOfModels
        (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj
          ((DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤
            max J O).objPreimage E))
        (injectiveModel ((derivedPullback G b h).obj F)) :=
  strictPreIso
    (pulledModelMap G b h
      (Functor.objObjPreimageIso
        (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O) E))
    ((derivedPullback G b h).obj F)
    (lift_quasiIso _ _ (pulledModelIso G b h
      (Functor.objObjPreimageIso
        (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O) E)))

/-- Exact inverse image carries derived sheaf internal Hom to the derived internal Hom of
the inverse images, through ordinary pullback of evaluation and K-injective representatives. -/
def comparison (E F : max J O) :
    (ExactFunctor.mapDerivedCategory
      (⟨SheafOfModules.pullback.{max u v} (ringMap G b), h⟩ :
        ringedSiteModuleCategory J O ⥤ₑ ringedSiteModuleCategory K O')).obj (obj E F) ⟶
      obj ((ExactFunctor.mapDerivedCategory
        (⟨SheafOfModules.pullback.{max u v} (ringMap G b), h⟩ :
          ringedSiteModuleCategory J O ⥤ₑ ringedSiteModuleCategory K O')).obj E)
        ((ExactFunctor.mapDerivedCategory
          (⟨SheafOfModules.pullback.{max u v} (ringMap G b), h⟩ :
            ringedSiteModuleCategory J O ⥤ₑ ringedSiteModuleCategory K O')).obj F) :=
  let A := (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤
    max J O).objPreimage E
  (exactPullback G b h).obj.mapDerivedCategoryFactors.hom.app
      ((strictInternalHom.obj (op A)).obj (injectiveModel F)) ≫
    DerivedCategory.Q.map
      (complexComparison G b A (injectiveModel F) ≫
        (strictInternalHom.obj
          (op (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex (.up ℤ)).obj A))).map
            (pulledModelMap G b h (injectiveModelIso F))) ≫
    (pulledSourceIso G b h E F).inv ≫
    (modelComparisonIso ((derivedPullback G b h).obj E)
      ((derivedPullback G b h).obj F)).hom

/-- After transport to the chosen source and K-injective target representatives, the
derived comparison is the localization of the complex comparison and target-model map. -/
theorem comparison_model (E F : max J O) :
    let P : ringedSiteModuleCategory J O ⥤ₑ ringedSiteModuleCategory K O' :=
      ⟨SheafOfModules.pullback.{max u v} (ringMap G b), h⟩
    let factors := @CategoryTheory.Functor.mapDerivedCategoryFactors
      _ _ _ _ _ _ _ _ P.obj inferInstance P.property.1 P.property.2
    let Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O := DerivedCategory.Q
    let A := Q.objPreimage E
    let PA := (P.obj.mapHomologicalComplex (.up ℤ)).obj A
    let PI := (P.obj.mapHomologicalComplex (.up ℤ)).obj (injectiveModel F)
    let s := liftToInjectiveModel PA (P.mapDerivedCategory.obj E)
      (factors.inv.app A ≫
        P.mapDerivedCategory.map (CategoryTheory.Functor.objObjPreimageIso Q E).hom)
    let t := liftToInjectiveModel PI (P.mapDerivedCategory.obj F)
      (factors.inv.app (injectiveModel F) ≫
        P.mapDerivedCategory.map (injectiveModelIso F).hom)
    factors.inv.app
        ((strictInternalHom.obj (op A)).obj (injectiveModel F)) ≫
      comparison G b h E F ≫
      (modelComparisonIso (P.mapDerivedCategory.obj E) (P.mapDerivedCategory.obj F)).inv ≫
      DerivedCategory.Q.map
        ((strictInternalHom.map s.op).app (injectiveModel (P.mapDerivedCategory.obj F))) =
    DerivedCategory.Q.map
      (complexComparison G b A (injectiveModel F) ≫
        (strictInternalHom.obj (op PA)).map t) := by
  let A := (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤
    max J O).objPreimage E
  let e := (exactPullback G b h).obj.mapDerivedCategoryFactors.app
    ((strictInternalHom.obj (op A)).obj (injectiveModel F))
  let m : _ ⟶ objOfModels
      (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex
        (.up ℤ)).obj A) (injectiveModel ((derivedPullback G b h).obj F)) :=
    DerivedCategory.Q.map
    (complexComparison G b A (injectiveModel F) ≫
      (strictInternalHom.obj (op
        (((SheafOfModules.pullback.{max u v} (ringMap G b)).mapHomologicalComplex
          (.up ℤ)).obj A))).map (pulledModelMap G b h (injectiveModelIso F)))
  let i := pulledSourceIso G b h E F
  let j := modelComparisonIso ((derivedPullback G b h).obj E)
    ((derivedPullback G b h).obj F)
  change e.inv ≫ (e.hom ≫ m ≫ i.inv ≫ j.hom) ≫ j.inv ≫ i.hom = m
  simp only [CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id_assoc,
    CategoryTheory.Iso.inv_hom_id_assoc]
  rw [i.inv_hom_id, CategoryTheory.Category.comp_id]

/-- The derived pullback comparison is contravariantly natural in the first object and
covariantly natural in the second object. -/
theorem naturality {E₁ E₂ F₁ F₂ : max J O} (f : E₂ ⟶ E₁) (g : F₁ ⟶ F₂) :
    (ExactFunctor.mapDerivedCategory
      (⟨SheafOfModules.pullback.{max u v} (ringMap G b), h⟩ :
        ringedSiteModuleCategory J O ⥤ₑ ringedSiteModuleCategory K O')).map (map f g) ≫ comparison G b h E₂ F₂ =
      comparison G b h E₁ F₁ ≫
        map ((ExactFunctor.mapDerivedCategory
      (⟨SheafOfModules.pullback.{max u v} (ringMap G b), h⟩ :
        ringedSiteModuleCategory J O ⥤ₑ ringedSiteModuleCategory K O')).map f) ((ExactFunctor.mapDerivedCategory
      (⟨SheafOfModules.pullback.{max u v} (ringMap G b), h⟩ :
        ringedSiteModuleCategory J O ⥤ₑ ringedSiteModuleCategory K O')).map g) := by
  sorry

end SheafOfModules.Pullback.DerivedInternalHom
