module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import ReasLib.CategoryTheory.Homology.DoubleComplex.MapTotal.PreservesColimits

/-! # Tensor comparison for unbounded derived pullback of étale modules -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory CategoryTheory.Functor
open CategoryTheory.MonoidalCategory ComplexShape

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
variable {S : Scheme.{u}}

/-- Termwise pullback of a tensor bicomplex admits a total complex. -/
instance modulesPullbackMappedTensorBicomplex_hasTotal {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) K L).HasTotal (up ℤ) := by
  intro n
  infer_instance

/-- The tensor bicomplex of termwise pullbacks admits a total complex. -/
instance modulesPullbackTensorBicomplexMap_hasTotal {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (Functor.Cochain.tensorBicomplexMap (Modules.pullback f) K L).HasTotal (up ℤ) := by
  intro n
  infer_instance

/-- The pointwise pullback tensor comparison commutes with the first bicomplex differential. -/
theorem modulesPullback_tensorBicomplex_comm₁ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) (i₁ i₁' i₂ : ℤ) (h : (up ℤ).Rel i₁ i₁') :
    Modules.DirectTensorComparison.pullbackTensor f (K.X i₁) (L.X i₂) ≫
        ((Functor.Cochain.tensorBicomplexMap (Modules.pullback f) K L).d i₁ i₁').f i₂ =
      ((Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) K L).d i₁ i₁').f i₂ ≫
        Modules.DirectTensorComparison.pullbackTensor f (K.X i₁') (L.X i₂) :=
  sorry

/-- The pointwise pullback tensor comparison commutes with the second bicomplex differential. -/
theorem modulesPullback_tensorBicomplex_comm₂ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) (i₁ i₂ i₂' : ℤ) (h : (up ℤ).Rel i₂ i₂') :
    Modules.DirectTensorComparison.pullbackTensor f (K.X i₁) (L.X i₂) ≫
        ((Functor.Cochain.tensorBicomplexMap (Modules.pullback f) K L).X i₁).d i₂ i₂' =
      ((Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) K L).X i₁).d i₂ i₂' ≫
        Modules.DirectTensorComparison.pullbackTensor f (K.X i₁) (L.X i₂') :=
  sorry

set_option maxRecDepth 4096 in
/-- Pointwise `f^*(M ⊗ N) ⟶ f^* M ⊗ f^* N` as a morphism of tensor bicomplexes. -/
noncomputable def modulesPullback_tensorBicomplexHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) K L ⟶ Functor.Cochain.tensorBicomplexMap (Modules.pullback f) K L :=
  HomologicalComplex₂.homMk (K := Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) K L)
    (L := Functor.Cochain.tensorBicomplexMap (Modules.pullback f) K L)
    (fun pq ↦ Modules.DirectTensorComparison.pullbackTensor f (K.X pq.1) (L.X pq.2))
    (modulesPullback_tensorBicomplex_comm₁ f K L)
    (modulesPullback_tensorBicomplex_comm₂ f K L)

/-- Additive-functor/total comparison for pullback of a tensor bicomplex is invertible. -/
theorem isIso_modulesPullback_totalComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    IsIso
      (HomologicalComplex₂.Total.Map.Comparison.hom (Modules.pullback f)
        (Functor.Cochain.tensorBicomplex K L) (up ℤ)) :=
  HomologicalComplex₂.Total.Map.Comparison.isIso_of_preservesColimits
    (Modules.pullback f) (Functor.Cochain.tensorBicomplex K L) (up ℤ)

/-- Cochain-level oplax comparison `f^*(K ⊗ L) ⟶ f^* K ⊗ f^* L`. -/
noncomputable def modulesPullback_cochainTensorComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj (K ⊗ L) ⟶
      ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K ⊗
        ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj L :=
  (@asIso _ _ _ _
      (HomologicalComplex₂.Total.Map.Comparison.hom (Modules.pullback f)
        (Functor.Cochain.tensorBicomplex K L) (up ℤ))
      (isIso_modulesPullback_totalComparison f K L)).inv ≫
    HomologicalComplex₂.total.map (modulesPullback_tensorBicomplexHom f K L) (up ℤ)

/-- The cochain comparison is the inverse total comparison followed by the totalized tensorator. -/
theorem modulesPullback_cochainTensorComparison_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    modulesPullback_cochainTensorComparison f K L =
      (@asIso _ _ _ _
          (HomologicalComplex₂.Total.Map.Comparison.hom (Modules.pullback f)
            (Functor.Cochain.tensorBicomplex K L) (up ℤ))
          (isIso_modulesPullback_totalComparison f K L)).inv ≫
        HomologicalComplex₂.total.map (modulesPullback_tensorBicomplexHom f K L) (up ℤ) :=
  by rfl

/-- The cochain-level counit `Lf^*(Q K) ⟶ Q(f^* K)` of derived module pullback. -/
noncomputable def modulePullbackDerived_cochainCounit {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (K : CochainComplex (Modules Y) ℤ) :
    (LeftDerived.Homotopy.functor (Modules.pullback f)).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K) :=
  (LeftDerived.Homotopy.functor (Modules.pullback f)).map
      ((DerivedCategory.quotientCompQhIso (Modules Y)).inv.app K) ≫
    ((Homotopy.toDerived (Modules.pullback f)).totalLeftDerivedCounit
        (DerivedCategory.Qh : HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)
        (HomotopyCategory.quasiIso (Modules Y) (up ℤ))).app
      ((HomotopyCategory.quotient (Modules Y) (up ℤ)).obj K) ≫
    (Homotopy.cochainIso (Modules.pullback f)).hom.app K

/-- `modulePullbackDerived_cochainCounit` is the total left-derived counit transported along
`quotientCompQhIso` and the homotopy-to-cochain comparison. -/
theorem modulePullbackDerived_cochainCounit_eq {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (K : CochainComplex (Modules Y) ℤ) :
    modulePullbackDerived_cochainCounit f K =
      (LeftDerived.Homotopy.functor (Modules.pullback f)).map
          ((DerivedCategory.quotientCompQhIso (Modules Y)).inv.app K) ≫
        ((Homotopy.toDerived (Modules.pullback f)).totalLeftDerivedCounit
            (DerivedCategory.Qh : HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)
            (HomotopyCategory.quasiIso (Modules Y) (up ℤ))).app
          ((HomotopyCategory.quotient (Modules Y) (up ℤ)).obj K) ≫
        (Homotopy.cochainIso (Modules.pullback f)).hom.app K :=
  by rfl

/-- Underived cochain-level source `Q(f^*K ⊗ f^*L)` of the derived pullback tensor comparison. -/
noncomputable abbrev modulePullbackCochainTensorSource {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CochainComplex (Modules Y) ℤ × CochainComplex (Modules Y) ℤ ⥤ ModuleDerived X :=
  ((Modules.pullback f).mapHomologicalComplex (up ℤ)).prod
      ((Modules.pullback f).mapHomologicalComplex (up ℤ)) ⋙
    tensor (CochainComplex (Modules X) ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X)

/-- Derived functor `Lf^*(A ⊗^L B)` in two variables. -/
noncomputable abbrev moduleDerivedTensorThenPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived Y × ModuleDerived Y ⥤ ModuleDerived X :=
  DerivedTensor.Bifunctor.functor (C := Modules Y) ⋙ LeftDerived.Homotopy.functor (Modules.pullback f)

/-- Derived functor `Lf^*A ⊗^L Lf^*B` in two variables. -/
noncomputable abbrev moduleDerivedPullbackThenTensor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived Y × ModuleDerived Y ⥤ ModuleDerived X :=
  (LeftDerived.Homotopy.functor (Modules.pullback f)).prod (LeftDerived.Homotopy.functor (Modules.pullback f)) ⋙
    DerivedTensor.Bifunctor.functor (C := Modules X)

/-- Counit of `Lf^*A ⊗^L Lf^*B` against the cochain-level source `Q(f^*K ⊗ f^*L)`. -/
noncomputable def moduleDerivedPullbackThenTensorCounit {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y).prod
        (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
      moduleDerivedPullbackThenTensor f ⟶
    modulePullbackCochainTensorSource f where
  app KL :=
    (DerivedTensor.Bifunctor.functor (C := Modules X)).map
        (Prod.mkHom
          (modulePullbackDerived_cochainCounit f KL.1)
          (modulePullbackDerived_cochainCounit f KL.2)) ≫
      DerivedTensor.Bifunctor.counitAppOfQ
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj KL.1)
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj KL.2)
  naturality _ _ _ := sorry

/-- The component of `moduleDerivedPullbackThenTensorCounit` is the pair of cochain counits
followed by the two-variable derived-tensor counit. -/
theorem moduleDerivedPullbackThenTensorCounit_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (moduleDerivedPullbackThenTensorCounit f).app (K, L) =
      (DerivedTensor.Bifunctor.functor (C := Modules X)).map
          (Prod.mkHom
            (modulePullbackDerived_cochainCounit f K)
            (modulePullbackDerived_cochainCounit f L)) ≫
        DerivedTensor.Bifunctor.counitAppOfQ
          (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K)
          (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj L) :=
  by rfl

/-- Counit of `Lf^*(A ⊗^L B)` against the cochain-level source `Q(f^*K ⊗ f^*L)`. -/
noncomputable def moduleDerivedTensorThenPullbackCounit {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y).prod
        (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
      moduleDerivedTensorThenPullback f ⟶
    modulePullbackCochainTensorSource f where
  app KL :=
    (LeftDerived.Homotopy.functor (Modules.pullback f)).map (DerivedTensor.Bifunctor.counitAppOfQ KL.1 KL.2) ≫
      modulePullbackDerived_cochainCounit f (KL.1 ⊗ KL.2) ≫
      DerivedCategory.Q.map (modulesPullback_cochainTensorComparison f KL.1 KL.2)
  naturality _ _ _ := sorry

/-- The component of `moduleDerivedTensorThenPullbackCounit` is derived pullback of the tensor
counit, followed by the cochain counit and the cochain-level pullback tensorator. -/
theorem moduleDerivedTensorThenPullbackCounit_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (moduleDerivedTensorThenPullbackCounit f).app (K, L) =
      (LeftDerived.Homotopy.functor (Modules.pullback f)).map (DerivedTensor.Bifunctor.counitAppOfQ K L) ≫
        modulePullbackDerived_cochainCounit f (K ⊗ L) ≫
        DerivedCategory.Q.map (modulesPullback_cochainTensorComparison f K L) :=
  by rfl

namespace CellTensorPullback

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Ordinary pullback of the specified cell replacement of an input complex. -/
abbrev pulledCell (K : CochainComplex Y.Modules ℤ) : CochainComplex X.Modules ℤ :=
  ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj
    ((Modules.CellTensor.replacement Y).obj K)

/-- Resolve both original inputs, pull back their actual cells, tensor, and localize. -/
def cochain : CochainComplex Y.Modules ℤ × CochainComplex Y.Modules ℤ ⥤ ModuleDerived X :=
  (Modules.CellTensor.replacement Y).prod (Modules.CellTensor.replacement Y) ⋙
    modulePullbackCochainTensorSource f

/-- The two augmentations from cell replacements of the already pulled-back cell complexes. -/
def tensorAugmentation (A : CochainComplex Y.Modules ℤ × CochainComplex Y.Modules ℤ) :
    (Modules.CellTensor.replacement X).obj (pulledCell f A.1) ⊗
        (Modules.CellTensor.replacement X).obj (pulledCell f A.2) ⟶
      pulledCell f A.1 ⊗ pulledCell f A.2 :=
  (Modules.CellTensor.augmentation X).app (pulledCell f A.1) ⊗ₘ
    (Modules.CellTensor.augmentation X).app (pulledCell f A.2)

/-- Derived pullback on an original input is computed by its specified pulled-back cells. -/
def pullbackComputation (K : CochainComplex Y.Modules ℤ) :
    (LeftDerived.Homotopy.functor (Modules.pullback f)).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (pulledCell f K) :=
  ((ModuleDerived.pullbackIsoTotalLeftDerived f).app (DerivedCategory.Q.obj K)).symm ≪≫
    (Modules.CellModels.pullbackUsingCells_fac f).app K

/-- Compute pullback-then-tensor using the actual pullback cells and the formal inverses
of the specified tensor augmentation, with no inverse chosen for an abstract comparison. -/
def computationOnInput
    (h : ∀ A, QuasiIso (tensorAugmentation f A))
    (A : CochainComplex Y.Modules ℤ × CochainComplex Y.Modules ℤ) :
    (moduleDerivedPullbackThenTensor f).obj
        (DerivedCategory.Q.obj A.1, DerivedCategory.Q.obj A.2) ≅ (cochain f).obj A :=
  (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
      ((pullbackComputation f A.1).prod (pullbackComputation f A.2)) ≪≫
    Modules.CellTensor.computationIso X (pulledCell f A.1) (pulledCell f A.2) ≪≫
    Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso X.Modules (up ℤ))
      (tensorAugmentation f A) (h A)

/-- The actual pullback-cell functor inverts product quasi-isomorphisms; its model augmentation
is acyclic. Tensor augmentations concern the pulled-back cell complexes, which are K-flat.
The displayed computation is natural and preserves the original cochain counit. -/
theorem model_laws :
    (Modules.CellTensor.denominators Y).IsInvertedBy (cochain f) ∧
    (∀ A, IsIso ((modulePullbackCochainTensorSource f).map
      ((Modules.CellTensor.pairAugmentation Y).app
        (((Modules.CellTensor.replacement Y).prod (Modules.CellTensor.replacement Y)).obj A)))) ∧
    (∀ A, QuasiIso (tensorAugmentation f A)) ∧
    (∀ (h : ∀ A, QuasiIso (tensorAugmentation f A))
      {A B : CochainComplex Y.Modules ℤ × CochainComplex Y.Modules ℤ} (a : A ⟶ B),
      (((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules))) ⋙
        moduleDerivedPullbackThenTensor f).map a ≫ (computationOnInput f h B).hom =
      (computationOnInput f h A).hom ≫ (cochain f).map a) ∧
    (∀ (h : ∀ A, QuasiIso (tensorAugmentation f A)) A,
      (computationOnInput f h A).hom ≫ (modulePullbackCochainTensorSource f).map
        ((Modules.CellTensor.pairAugmentation Y).app A) =
      (moduleDerivedPullbackThenTensorCounit f).app A) := sorry

/-- Native product localization of the specified pulled-back cell-tensor functor. -/
def derived : ModuleDerived Y × ModuleDerived Y ⥤ ModuleDerived X :=
  Localization.lift (cochain f) (model_laws f).1
    ((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)))

/-- The native computation isomorphism of the pulled-back cell model. -/
def fac : (DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)) ⋙ derived f ≅ cochain f :=
  Localization.fac (cochain f) (model_laws f).1
    ((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)))

/-- The original pullback-then-tensor functor computes the specified pulled-back cell tensor. -/
def computationIso :
    (DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)) ⋙
      moduleDerivedPullbackThenTensor f ≅ cochain f :=
  NatIso.ofComponents (computationOnInput f (model_laws f).2.2.1)
    (fun a ↦ (model_laws f).2.2.2.1 (model_laws f).2.2.1 a)

/-- The original functor and the native localization model are compared by descending
both directions of the displayed cochain computation. -/
def comparisonIso : moduleDerivedPullbackThenTensor f ≅ derived f :=
  Localization.liftNatIso ((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)))
    (Modules.CellTensor.denominators Y)
    (((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules))) ⋙
      moduleDerivedPullbackThenTensor f)
    (((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules))) ⋙ derived f)
    (moduleDerivedPullbackThenTensor f) (derived f)
    (computationIso f ≪≫ (fac f).symm)

/-- The native model counit applies ordinary pullback and tensor to the actual pair augmentation. -/
def counit : (DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)) ⋙ derived f ⟶
    modulePullbackCochainTensorSource f :=
  LeftDerived.Deformation.counit _
    ((Modules.CellTensor.replacement Y).prod (Modules.CellTensor.replacement Y))
    (Modules.CellTensor.pairAugmentation Y) (modulePullbackCochainTensorSource f)
    (derived f) (fac f)

private theorem pairAugmentation_mem (A) :
    Modules.CellTensor.denominators Y ((Modules.CellTensor.pairAugmentation Y).app A) :=
  ⟨SheafOfModules.CellReplacement.augmentation_quasiIso A.1,
    SheafOfModules.CellReplacement.augmentation_quasiIso A.2⟩

private theorem comparisonIso_counit :
    Functor.whiskerLeft ((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)))
        (comparisonIso f).hom ≫ counit f = moduleDerivedPullbackThenTensorCounit f := by
  ext A
  change (comparisonIso f).hom.app _ ≫ (counit f).app A = _
  have he := Localization.liftNatTrans_app
    ((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)))
    (Modules.CellTensor.denominators Y)
    (((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules))) ⋙
      moduleDerivedPullbackThenTensor f)
    (((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules))) ⋙ derived f)
    (moduleDerivedPullbackThenTensor f) (derived f)
    (computationIso f ≪≫ (fac f).symm).hom A
  rw [show (comparisonIso f).hom.app _ =
    (computationIso f).hom.app A ≫ (fac f).inv.app A by
      simpa only [comparisonIso, Localization.liftNatIso_hom, Localization.Lifting.iso,
        Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.refl_hom, Iso.refl_inv,
        NatTrans.id_app, Category.id_comp, Category.comp_id] using he]
  change ((computationIso f).hom.app A ≫ (fac f).inv.app A) ≫
      ((fac f).hom.app A ≫ (modulePullbackCochainTensorSource f).map
        ((Modules.CellTensor.pairAugmentation Y).app A) ≫ 𝟙 _) = _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Category.comp_id]
  exact (model_laws f).2.2.2.2 (model_laws f).2.2.1 A

/-- The native model's terminal extension witness uses the actual augmentation-based maps. -/
def modelTerminalWitness : (RightExtension.mk (derived f) (counit f)).IsUniversal :=
  LeftDerived.Deformation.terminalWitness
    ((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)))
    (Modules.CellTensor.denominators Y)
    ((Modules.CellTensor.replacement Y).prod (Modules.CellTensor.replacement Y))
    (Modules.CellTensor.pairAugmentation Y) (by exact pairAugmentation_mem (Y := Y))
    (modulePullbackCochainTensorSource f) (derived f) (fac f) (model_laws f).2.1

/-- The specified extension maps are the native cell-model lifts transported through computation. -/
def extensionLift (G : ModuleDerived Y × ModuleDerived Y ⥤ ModuleDerived X)
    (β : (DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)) ⋙ G ⟶
      modulePullbackCochainTensorSource f) : G ⟶ moduleDerivedPullbackThenTensor f :=
  LeftDerived.Deformation.extensionLift
    ((DerivedCategory.Q (C := Y.Modules)).prod (DerivedCategory.Q (C := Y.Modules)))
    (Modules.CellTensor.denominators Y)
    ((Modules.CellTensor.replacement Y).prod (Modules.CellTensor.replacement Y))
    (Modules.CellTensor.pairAugmentation Y) (by exact pairAugmentation_mem (Y := Y))
    (modulePullbackCochainTensorSource f) (derived f) (fac f) G β ≫ (comparisonIso f).inv

/-- The original counit retains the constructed universal maps after computation transport. -/
def terminalWitness :
    (RightExtension.mk (moduleDerivedPullbackThenTensor f)
      (moduleDerivedPullbackThenTensorCounit f)).IsUniversal :=
  (modelTerminalWitness f).ofIso
    (CostructuredArrow.isoMk (comparisonIso f).symm (by
      ext A
      have h := NatTrans.congr_app (comparisonIso_counit f) A
      change (comparisonIso f).inv.app _ ≫ (moduleDerivedPullbackThenTensorCounit f).app A = _
      change (comparisonIso f).hom.app _ ≫ (counit f).app A =
        (moduleDerivedPullbackThenTensorCounit f).app A at h
      rw [← h]
      simp))

end CellTensorPullback

/-- Pullback followed by tensor is left derived through its specified cochain counit. -/
instance moduleDerivedPullbackThenTensor_isLeftDerived {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (moduleDerivedPullbackThenTensor f).IsLeftDerivedFunctor
      (moduleDerivedPullbackThenTensorCounit f) (Modules.CellTensor.denominators Y) where
  isRightKanExtension :=
    { nonempty_isUniversal := ⟨CellTensorPullback.terminalWitness f⟩ }


/-- The derived comparison `Lf^*(A ⊗^L B) ⟶ Lf^*A ⊗^L Lf^*B` as a natural transformation. -/
noncomputable def moduleDerivedPullbackTensorComparisonNatTrans {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    moduleDerivedTensorThenPullback f ⟶ moduleDerivedPullbackThenTensor f :=
  (moduleDerivedPullbackThenTensor f).leftDerivedLift
    (moduleDerivedPullbackThenTensorCounit f)
    ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
      (HomologicalComplex.quasiIso (Modules Y) (up ℤ)))
    (moduleDerivedTensorThenPullback f)
    (moduleDerivedTensorThenPullbackCounit f)

/-- `moduleDerivedPullbackTensorComparisonNatTrans` is the left-derived lift of the
tensor-then-pullback counit against the pullback-then-tensor model. -/
theorem moduleDerivedPullbackTensorComparisonNatTrans_eq {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    moduleDerivedPullbackTensorComparisonNatTrans f =
      (moduleDerivedPullbackThenTensor f).leftDerivedLift
        (moduleDerivedPullbackThenTensorCounit f)
        ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
          (HomologicalComplex.quasiIso (Modules Y) (up ℤ)))
        (moduleDerivedTensorThenPullback f)
        (moduleDerivedTensorThenPullbackCounit f) :=
  by rfl

/-- Ambient derived comparison `Lf^*(A ⊗^L B) ⟶ Lf^*A ⊗^L Lf^*B`. -/
noncomputable def moduleDerivedPullbackTensorComparison {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (A B : ModuleDerived Y) :
    (LeftDerived.Homotopy.functor (Modules.pullback f)).obj
        ((DerivedTensor.Bifunctor.functor (C := Modules Y)).obj (A, B)) ⟶
      (DerivedTensor.Bifunctor.functor (C := Modules X)).obj
        ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj A, (LeftDerived.Homotopy.functor (Modules.pullback f)).obj B) :=
  (moduleDerivedPullbackTensorComparisonNatTrans f).app (A, B)

/-- `moduleDerivedPullbackTensorComparison` is the component of the derived comparison
natural transformation. -/
theorem moduleDerivedPullbackTensorComparison_eq {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (A B : ModuleDerived Y) :
    moduleDerivedPullbackTensorComparison f A B =
      (moduleDerivedPullbackTensorComparisonNatTrans f).app (A, B) :=
  by rfl

/-- Derived pullback comparison on the fixed-right tensor `Lf^*(A ⊗^L B) ⟶ Lf^* A ⊗^L Lf^* B`. -/
noncomputable def rightTensorComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A B : ModuleDerived Y) :
    (LeftDerived.Homotopy.functor (Modules.pullback f)).obj ((DerivedTensor.Right.functor B).obj A) ⟶
      (DerivedTensor.Right.functor ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj B)).obj
        ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj A) :=
  (LeftDerived.Homotopy.functor (Modules.pullback f)).map (DerivedTensor.Bifunctor.Right.isoAppOf B
      (Modules.hasDerivedTensorRightCompatible Y B) A).hom ≫
    moduleDerivedPullbackTensorComparison f A B ≫
      (DerivedTensor.Bifunctor.Right.isoAppOf
        ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj B)
        (Modules.hasDerivedTensorRightCompatible X _)
        ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj A)).inv

/-- `rightTensorComparison` is the two-variable derived comparison conjugated by the
fixed-right/two-variable identifications. -/
theorem rightTensorComparison_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A B : ModuleDerived Y) :
    rightTensorComparison f A B =
      (LeftDerived.Homotopy.functor (Modules.pullback f)).map (DerivedTensor.Bifunctor.Right.isoAppOf B
      (Modules.hasDerivedTensorRightCompatible Y B) A).hom ≫
        moduleDerivedPullbackTensorComparison f A B ≫
          (DerivedTensor.Bifunctor.Right.isoAppOf
            ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj B)
            (Modules.hasDerivedTensorRightCompatible X _)
            ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj A)).inv :=
  by rfl

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
