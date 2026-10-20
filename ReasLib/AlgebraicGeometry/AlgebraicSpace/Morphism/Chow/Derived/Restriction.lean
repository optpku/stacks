module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Chow.Derived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.SectionTensor

/-! # Restriction of Fourier–Mukai complexes along derived Chow presentations -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.DerivedCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory ComplexShape
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open DerivedTensor.Bifunctor

noncomputable section
set_option backward.isDefEq.respectTransparency false
-- The public comparison retains private implementations of its canonical composition maps.
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedChowPresentation

private def pushforwardComposition {S : Scheme.{u}} {T U V : AlgebraicSpace S}
    (f : T ⟶ U) (g : U ⟶ V) :
    Modules.moduleDerivedPushforward f ⋙ Modules.moduleDerivedPushforward g ≅
      Modules.moduleDerivedPushforward (f ≫ g) :=
  (((Modules.derivedPullbackPushforwardAdjunction g).comp
    (Modules.derivedPullbackPushforwardAdjunction f)).ofNatIsoLeft
      (asIso (modulePullbackDerived.compComparison f g))).rightAdjointUniq
        (Modules.derivedPullbackPushforwardAdjunction (f ≫ g))

private def pullbackSingleComparison {S : Scheme.{u}} {T U : AlgebraicSpace S}
    (f : T ⟶ U) (F : U.Modules) :
    (modulePullbackDerived f).obj ((DerivedCategory.singleFunctor U.Modules 0).obj F) ⟶
      (DerivedCategory.singleFunctor T.Modules 0).obj ((Modules.pullback f).obj F) :=
  modulePullbackDerived_cochainCounit f
    ((HomologicalComplex.single U.Modules (up ℤ) 0).obj F) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (Modules.pullback f) (up ℤ) 0).hom.app F)

private def tensorColumnIso {S : Scheme.{u}} {T U : AlgebraicSpace S}
    (f : T ⟶ U) (C D : CochainComplex U.Modules ℤ) (a : ℤ) :
    (Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) C D).X a ≅
      (Functor.Cochain.tensorBicomplexMap (Modules.pullback f) C D).X a :=
  HomologicalComplex.Hom.isoOfComponents
    (fun b ↦ Modules.PullbackTensor.tensorIso f (C.X a) (D.X b))
    (modulesPullback_tensorBicomplex_comm₂ f C D a)

private def tensorBicomplexIso {S : Scheme.{u}} {T U : AlgebraicSpace S}
    (f : T ⟶ U) (C D : CochainComplex U.Modules ℤ) :
    Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) C D ≅
      Functor.Cochain.tensorBicomplexMap (Modules.pullback f) C D :=
  HomologicalComplex.Hom.isoOfComponents (tensorColumnIso f C D) (by
    intro a b hab
    apply HomologicalComplex.Hom.ext
    funext n
    exact modulesPullback_tensorBicomplex_comm₁ f C D a b n hab)

private def totalComparisonInvComponent {S : Scheme.{u}} {T U : AlgebraicSpace S}
    (f : T ⟶ U) (C D : CochainComplex U.Modules ℤ) (n : ℤ) :
    (Modules.pullback f).obj (((Functor.Cochain.tensorBicomplex C D).total (up ℤ)).X n) ⟶
      ((Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) C D).total (up ℤ)).X n :=
  ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    ((Functor.Cochain.tensorBicomplex C D).totalDesc (fun a b h ↦
      (Modules.pullbackPushforwardAdjunction f).unit.app
          (((Functor.Cochain.tensorBicomplex C D).X a).X b) ≫
        (Modules.pushforward f).map
          ((Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) C D).ιTotal
            (up ℤ) a b n h)))

private theorem map_ι_totalComparisonInvComponent {S : Scheme.{u}}
    {T U : AlgebraicSpace S} (f : T ⟶ U) (C D : CochainComplex U.Modules ℤ)
    (a b n : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (a, b) = n) :
    (Modules.pullback f).map
        ((Functor.Cochain.tensorBicomplex C D).ιTotal (up ℤ) a b n h) ≫
        totalComparisonInvComponent f C D n =
      (Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) C D).ιTotal
        (up ℤ) a b n h := by
  rw [totalComparisonInvComponent,
    ← Adjunction.homEquiv_naturality_left_symm, HomologicalComplex₂.ι_totalDesc,
    ← Adjunction.homEquiv_unit]
  exact Equiv.symm_apply_apply _ _

private def totalComparisonComponentIso {S : Scheme.{u}} {T U : AlgebraicSpace S}
    (f : T ⟶ U) (C D : CochainComplex U.Modules ℤ) (n : ℤ) :
    ((Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) C D).total (up ℤ)).X n ≅
      (Modules.pullback f).obj (((Functor.Cochain.tensorBicomplex C D).total (up ℤ)).X n) where
  hom := HomologicalComplex₂.Total.Map.Comparison.component (Modules.pullback f)
    (Functor.Cochain.tensorBicomplex C D) (up ℤ) n
  inv := totalComparisonInvComponent f C D n
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro a b h
    rw [← Category.assoc, HomologicalComplex₂.Total.Map.Comparison.ι_component,
      map_ι_totalComparisonInvComponent]
    simp only [Category.comp_id]
  inv_hom_id := by
    apply ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    simp only [totalComparisonInvComponent, Equiv.apply_symm_apply, Adjunction.homEquiv_id]
    apply HomologicalComplex₂.total.hom_ext
    intro a b h
    rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc, Category.assoc,
      ← Functor.map_comp, HomologicalComplex₂.Total.Map.Comparison.ι_component]
    exact ((Modules.pullbackPushforwardAdjunction f).unit.naturality _).symm

private def totalComparisonIso {S : Scheme.{u}} {T U : AlgebraicSpace S}
    (f : T ⟶ U) (C D : CochainComplex U.Modules ℤ) :
    (Functor.Cochain.mappedTensorBicomplex (Modules.pullback f) C D).total (up ℤ) ≅
      ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj
        ((Functor.Cochain.tensorBicomplex C D).total (up ℤ)) :=
  HomologicalComplex.Hom.isoOfComponents (totalComparisonComponentIso f C D)
    (HomologicalComplex₂.Total.Map.Comparison.component_comm (Modules.pullback f)
      (Functor.Cochain.tensorBicomplex C D) (up ℤ))

private def cochainTensorIso {S : Scheme.{u}} {T U : AlgebraicSpace S}
    (f : T ⟶ U) (C D : CochainComplex U.Modules ℤ) :
    ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj (C ⊗ D) ≅
      ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj C ⊗
        ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj D :=
  (totalComparisonIso f C D).symm ≪≫
    HomologicalComplex₂.total.mapIso (tensorBicomplexIso f C D) (up ℤ)

private def exactPullbackCochainIso {S : Scheme.{u}} {T U : AlgebraicSpace S}
    (f : T ⟶ U) [Etale f] (C : CochainComplex U.Modules ℤ) :
    (modulePullbackDerived f).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj C) :=
  ((ModuleDerived.pullbackIsoTotalLeftDerived f).app (DerivedCategory.Q.obj C)).symm ≪≫
    ModuleDerived.pullbackIsoMapDerivedCategoryOnInput f C ≪≫
      (Modules.pullback f).mapDerivedCategoryFactors.app C

private def tensorComputation {S : Scheme.{u}} (T : AlgebraicSpace S)
    (B C : ModuleDerived T) :
    (DerivedTensor.Right.functor C).obj B ≅ DerivedCategory.Q.obj
      ((Modules.CellTensor.replacement T).obj (DerivedCategory.Q.objPreimage B) ⊗
        (Modules.CellTensor.replacement T).obj (DerivedCategory.Q.objPreimage C)) :=
  Right.isoApp C B ≪≫
    (DerivedTensor.Bifunctor.functor (C := T.Modules)).mapIso
      ((DerivedCategory.Q.objObjPreimageIso B).symm.prod
        (DerivedCategory.Q.objObjPreimageIso C).symm) ≪≫
    Modules.CellTensor.computationIso T _ _

private def tensorPullbackIso {S : Scheme.{u}} {T U : AlgebraicSpace S}
    (f : T ⟶ U) [Etale f] (B C : ModuleDerived U) :
    (modulePullbackDerived f).obj ((DerivedTensor.Right.functor C).obj B) ≅
      (DerivedTensor.Right.functor ((modulePullbackDerived f).obj C)).obj
        ((modulePullbackDerived f).obj B) :=
  (modulePullbackDerived f).mapIso (tensorComputation U B C) ≪≫
    exactPullbackCochainIso f _ ≪≫
    DerivedCategory.Q.mapIso (cochainTensorIso f _ _) ≪≫
    (CellTensorPullback.computationOnInput f (CellTensorPullback.model_laws f).2.2.1
      (DerivedCategory.Q.objPreimage B, DerivedCategory.Q.objPreimage C)).symm ≪≫
    (DerivedTensor.Bifunctor.functor (C := T.Modules)).mapIso
      (((modulePullbackDerived f).mapIso (DerivedCategory.Q.objObjPreimageIso B)).prod
        ((modulePullbackDerived f).mapIso (DerivedCategory.Q.objObjPreimageIso C))) ≪≫
    (Right.isoApp _ _).symm

variable {A : Type u} [CommRing A]
  {X : AlgebraicSpace (Spec (CommRingCat.of A))}
  [Separated (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]
  {x : Points X}

/-- Restriction to `V` of `Rq_*(Lp^* K ⊗^L E)`, for the projections
`p = ProjectiveSpace.toBase M.n X` and `q = ProjectiveSpace.toOfScheme M.n X`. -/
noncomputable def fourierMukaiRestrict (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    ModuleDerived M.V.X :=
  let pullbackK := (modulePullbackDerived (ProjectiveSpace.toBase M.n X)).obj K.obj
  let tensored := (DerivedTensor.Right.functor M.E).obj pullbackK
  let pushed := (Modules.moduleDerivedPushforward (ProjectiveSpace.toOfScheme M.n X)).obj tensored
  (modulePullbackDerived M.V.ι).obj pushed

/-- `fourierMukaiRestrict` is the functor composite
`modulePullbackDerived p ⋙ DerivedTensor.Right.functor E ⋙
Modules.moduleDerivedPushforward q ⋙ modulePullbackDerived V.ι`. -/
theorem fourierMukaiRestrict_eq (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    fourierMukaiRestrict M K =
      (modulePullbackDerived (ProjectiveSpace.toBase M.n X) ⋙
          DerivedTensor.Right.functor M.E ⋙
          Modules.moduleDerivedPushforward (ProjectiveSpace.toOfScheme M.n X) ⋙
          modulePullbackDerived M.V.ι).obj
        K.obj := rfl

/-- Pushforward of `K|_W` along `W ⟶ V = M.preimageTo`, where restriction to `W`
is derived pullback along `M.preimageι ≫ M.sourceProjection`. -/
noncomputable def closedImmersionPushforward (M : DerivedChowPresentation x)
    (K : DerivedQCoh X) : ModuleDerived M.V.X :=
  let restrictK :=
    (modulePullbackDerived (M.preimageι ≫ M.sourceProjection)).obj K.obj
  (Modules.moduleDerivedPushforward M.preimageTo).obj restrictK

/-- `closedImmersionPushforward` is the functor composite
`modulePullbackDerived (W ⟶ X) ⋙ Modules.moduleDerivedPushforward (W ⟶ V)`. -/
theorem closedImmersionPushforward_eq (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    closedImmersionPushforward M K =
      (modulePullbackDerived (M.preimageι ≫ M.sourceProjection) ⋙
          Modules.moduleDerivedPushforward M.preimageTo).obj
        K.obj := rfl

/-- The comparison `W ⟶ V = c|_W` of a derived Chow presentation is of finite
presentation. -/
theorem finitePresentation_preimageTo (M : DerivedChowPresentation x) :
    FinitePresentation M.preimageTo := sorry

/-- The projection `q' : X ×_A V ⟶ V` of a derived Chow presentation. -/
private def ambientOpenTo (M : DerivedChowPresentation x) : M.ambientOpen ⟶ M.V.X :=
  Open.inverseImageTo (ProjectiveSpace.toOfScheme M.n X) M.V.ι M.V.isOpenImmersion.presheaf

/-- The cartesian square of `q = ProjectiveSpace.toOfScheme M.n X` along `M.V.ι`. -/
private theorem toOfScheme_openCommSq (M : DerivedChowPresentation x) :
    CommSq M.ambientOpenι M.ambientOpenTo
      (ProjectiveSpace.toOfScheme M.n X) M.V.ι :=
  ⟨pullback.condition (f := (homFunctor (ProjectiveSpace.toOfScheme M.n X))) (g := (homFunctor M.V.ι))⟩

/-- The cone of `W ⟶ X ×_A ℙⁿ_A` and `W ⟶ V` commutes over `ℙⁿ_A`. -/
private theorem preimageToAmbientOpen_w (M : DerivedChowPresentation x) :
    (M.preimageι ≫ M.immersion) ≫
        homFunctor (ProjectiveSpace.toOfScheme M.n X) =
      M.preimageTo ≫ homFunctor M.V.ι :=
  pullback.condition (f := (homFunctor M.projectiveProjection)) (g := (homFunctor M.V.ι))

/-- The closed immersion `i : W ⟶ X ×_A V` over `V`. -/
private def preimageToAmbientOpen (M : DerivedChowPresentation x) : M.preimage ⟶ M.ambientOpen :=
  (pullback.lift (f := (homFunctor (ProjectiveSpace.toOfScheme M.n X))) (g := (homFunctor M.V.ι))
      (M.preimageι ≫ M.immersion)
      M.preimageTo
      (preimageToAmbientOpen_w M) :
    M.preimage.functorOfPoints ⟶ M.ambientOpen.functorOfPoints)

/-- The cartesian square of the closed immersion `Z ⟶ X ×_A ℙⁿ_A` along `X ×_A V`. -/
private theorem immersion_openCommSq (M : DerivedChowPresentation x) :
    CommSq M.preimageι M.preimageToAmbientOpen M.immersion M.ambientOpenι :=
  ⟨(pullback.lift_fst (f := (homFunctor (ProjectiveSpace.toOfScheme M.n X))) (g := (homFunctor M.V.ι))
      (M.preimageι ≫ M.immersion) M.preimageTo
      (preimageToAmbientOpen_w M)).symm⟩

/-- `Lp^* K` on the ambient fibre product. -/
private def pullbackK (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    ModuleDerived M.ambient :=
  (modulePullbackDerived (ProjectiveSpace.toBase M.n X)).obj K.obj

/-- `Lp^* K ⊗^L E` on the ambient fibre product. -/
private def tensoredKernel (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    ModuleDerived M.ambient :=
  (DerivedTensor.Right.functor M.E).obj (pullbackK M K)

/-- Degree-zero structure sheaf of `W`. -/
private def preimageStructureSheaf (M : DerivedChowPresentation x) : ModuleDerived M.preimage :=
  (DerivedCategory.singleFunctor (Modules M.preimage) 0).obj
    (SheafOfModules.unit (structureSheaf M.preimage))

/-- Degree-zero structure sheaf of `Z`. -/
private def closedStructureSheaf (M : DerivedChowPresentation x) : ModuleDerived M.Z.X :=
  (DerivedCategory.singleFunctor (Modules M.Z.X) 0).obj
    (SheafOfModules.unit (structureSheaf M.Z.X))

/-- Replace `E|_{X ×_A V}` by the pushforward of `𝒪_Z` inside the restricted tensor. -/
private def restrictionReplaceHom (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    (modulePullbackDerived M.ambientOpenι).obj (tensoredKernel M K) ⟶
      (DerivedTensor.Right.functor
          ((modulePullbackDerived M.ambientOpenι).obj M.pushforwardStructureSheaf)).obj
        ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K)) :=
  let tensorBifunctor :
      ModuleDerived M.ambientOpen × ModuleDerived M.ambientOpen ⥤
        ModuleDerived M.ambientOpen :=
    DerivedTensor.Bifunctor.functor
  rightTensorComparison M.ambientOpenι (pullbackK M K) M.E ≫
    (Right.isoApp
        ((modulePullbackDerived M.ambientOpenι).obj M.E)
        ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))).hom ≫
      tensorBifunctor.map
          (Prod.mkHom (𝟙 ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K)))
            M.restrictionIso.hom) ≫
        (Right.isoApp
            ((modulePullbackDerived M.ambientOpenι).obj M.pushforwardStructureSheaf)
            ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))).inv

/-- The underived degree-zero pushforward of `𝒪_Z` maps to the derived pushforward. -/
private def underivedToDerivedPushforward (M : DerivedChowPresentation x) :
    M.pushforwardStructureSheaf ⟶
      (Modules.moduleDerivedPushforward M.immersion).obj M.closedStructureSheaf :=
  DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
          (Modules.pushforward M.immersion) (up ℤ) 0).inv.app
        (SheafOfModules.unit (structureSheaf M.Z.X))) ≫
    (Modules.moduleDerivedPushforward.unit M.immersion).app
      ((HomologicalComplex.single (Modules M.Z.X) (up ℤ) 0).obj
        (SheafOfModules.unit (structureSheaf M.Z.X)))

/-- Identify `(b, c)_* 𝒪_Z` restricted to `X ×_A V` with `Ri_* 𝒪_W`. -/
private def restrictedStructureToPushforward (M : DerivedChowPresentation x) :
    (modulePullbackDerived M.ambientOpenι).obj M.pushforwardStructureSheaf ⟶
      (Modules.moduleDerivedPushforward M.preimageToAmbientOpen).obj M.preimageStructureSheaf :=
  (modulePullbackDerived M.ambientOpenι).map (underivedToDerivedPushforward M) ≫
    Hom.DerivedBaseChange.app (immersion_openCommSq M) M.closedStructureSheaf ≫
      (Modules.moduleDerivedPushforward M.preimageToAmbientOpen).map
        (pullbackSingleComparison M.preimageι
            (SheafOfModules.unit (structureSheaf M.Z.X)) ≫
          (DerivedCategory.singleFunctor (Modules M.preimage) 0).map
            (IdealSubobject.pullbackUnit M.preimageι))

/-- Apply the projection-formula mate along `i : W ⟶ X ×_A V`. -/
private def projectionFormulaHom (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    (DerivedTensor.Right.functor
        ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))).obj
      ((Modules.moduleDerivedPushforward M.preimageToAmbientOpen).obj M.preimageStructureSheaf) ⟶
      (Modules.moduleDerivedPushforward M.preimageToAmbientOpen).obj
        ((DerivedTensor.Right.functor
            ((modulePullbackDerived M.preimageToAmbientOpen).obj
              ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K)))).obj
          M.preimageStructureSheaf) :=
  leftMate M.preimageToAmbientOpen M.preimageStructureSheaf
    ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))

/-- Identify `Li^* Lp^* K|_{X ×_A V}` with `K|_W`. -/
private def etalePullbackHom (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    (modulePullbackDerived M.preimageToAmbientOpen).obj
      ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K)) ⟶
      (modulePullbackDerived (M.preimageι ≫ M.sourceProjection)).obj K.obj :=
  (modulePullbackDerived M.preimageToAmbientOpen).map
      ((modulePullbackDerived.compComparison M.ambientOpenι
          (ProjectiveSpace.toBase M.n X)).app K.obj) ≫
    (modulePullbackDerived.compComparison M.preimageToAmbientOpen
        (M.ambientOpenι ≫ ProjectiveSpace.toBase M.n X)).app K.obj ≫
      eqToHom
        (congrArg (fun f : M.preimage ⟶ X ↦ (modulePullbackDerived f).obj K.obj)
          (congrArg (fun f : M.preimage ⟶ M.ambient ↦ f ≫ ProjectiveSpace.toBase M.n X)
            (pullback.lift_fst (f := (homFunctor (ProjectiveSpace.toOfScheme M.n X))) (g := (homFunctor M.V.ι))
              (M.preimageι ≫ M.immersion) M.preimageTo
              (preimageToAmbientOpen_w M))))

/-- The structure sheaf is the monoidal unit of `𝒪_W`-modules. -/
private def preimageStructureModuleUnitIso (M : DerivedChowPresentation x) :
    SheafOfModules.unit (structureSheaf M.preimage) ≅ 𝟙_ (Modules M.preimage) :=
  Modules.structureModuleIsoTensorUnit M.preimage

/-- The degree-zero monoidal unit complex is the monoidal unit of cochain complexes. -/
private def preimageUnitComplexIso (M : DerivedChowPresentation x) :
    ((HomologicalComplex.single (Modules M.preimage) (up ℤ) 0).obj
        (𝟙_ (Modules M.preimage))) ≅
      𝟙_ (CochainComplex (Modules M.preimage) ℤ) :=
  Iso.refl _

/-- Drop derived tensoring with `𝒪_W[0]` via the two-variable counit and the underived
right unitor. -/
private def tensorRightStructureSheafHom (M : DerivedChowPresentation x)
    (N : ModuleDerived M.preimage) :
    (DerivedTensor.Right.functor M.preimageStructureSheaf).obj N ⟶ N :=
  let tensorBifunctor :
      ModuleDerived M.preimage × ModuleDerived M.preimage ⥤
        ModuleDerived M.preimage :=
    DerivedTensor.Bifunctor.functor
  (Right.isoApp M.preimageStructureSheaf N).hom ≫
    tensorBifunctor.map
        (Prod.mkHom
          (DerivedCategory.Q.objObjPreimageIso N).inv
          ((DerivedCategory.singleFunctor (Modules M.preimage) 0).map
              (preimageStructureModuleUnitIso M).hom ≫
            DerivedCategory.Q.map (preimageUnitComplexIso M).hom)) ≫
      DerivedTensor.Bifunctor.counitAppOfQ
          ((DerivedCategory.Q : CochainComplex (Modules M.preimage) ℤ ⥤
              ModuleDerived M.preimage).objPreimage N)
          (𝟙_ (CochainComplex (Modules M.preimage) ℤ)) ≫
        DerivedCategory.Q.map
            (ρ_ ((DerivedCategory.Q : CochainComplex (Modules M.preimage) ℤ ⥤
                ModuleDerived M.preimage).objPreimage N)).hom ≫
          (DerivedCategory.Q.objObjPreimageIso N).hom

/-- Canonical comparison `Rq_*(Lp^* K ⊗^L E)|_V ⟶ R(W ⟶ V)_*(K|_W)`. -/
def fourierMukaiRestrict_hom (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    fourierMukaiRestrict M K ⟶ closedImmersionPushforward M K :=
  let tensorBifunctor :
      ModuleDerived M.ambientOpen × ModuleDerived M.ambientOpen ⥤
        ModuleDerived M.ambientOpen :=
    DerivedTensor.Bifunctor.functor
  Hom.DerivedBaseChange.app (toOfScheme_openCommSq M) (tensoredKernel M K) ≫
    (Modules.moduleDerivedPushforward M.ambientOpenTo).map (restrictionReplaceHom M K) ≫
      (Modules.moduleDerivedPushforward M.ambientOpenTo).map
          ((Right.isoApp
                ((modulePullbackDerived M.ambientOpenι).obj M.pushforwardStructureSheaf)
                ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))).hom ≫
            tensorBifunctor.map
                (Prod.mkHom
                  (𝟙 ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K)))
                  (restrictedStructureToPushforward M)) ≫
              (Right.isoApp
                  ((Modules.moduleDerivedPushforward M.preimageToAmbientOpen).obj
                    M.preimageStructureSheaf)
                  ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))).inv) ≫
        (Modules.moduleDerivedPushforward M.ambientOpenTo).map
            (Right.comm
              ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))
              ((Modules.moduleDerivedPushforward M.preimageToAmbientOpen).obj
                M.preimageStructureSheaf)).hom ≫
          (Modules.moduleDerivedPushforward M.ambientOpenTo).map (projectionFormulaHom M K) ≫
            (pushforwardComposition M.preimageToAmbientOpen M.ambientOpenTo).hom.app
                ((DerivedTensor.Right.functor
                    ((modulePullbackDerived M.preimageToAmbientOpen).obj
                      ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K)))).obj
                  M.preimageStructureSheaf) ≫
              eqToHom
                  (congrArg
                    (fun f : M.preimage ⟶ M.V.X ↦
                      (Modules.moduleDerivedPushforward f).obj
                        ((DerivedTensor.Right.functor
                            ((modulePullbackDerived M.preimageToAmbientOpen).obj
                              ((modulePullbackDerived M.ambientOpenι).obj
                                (pullbackK M K)))).obj
                          M.preimageStructureSheaf))
                    (pullback.lift_snd (f := (homFunctor (ProjectiveSpace.toOfScheme M.n X))) (g := (homFunctor M.V.ι))
                      (M.preimageι ≫ M.immersion) M.preimageTo
                      (preimageToAmbientOpen_w M))) ≫
                (Modules.moduleDerivedPushforward M.preimageTo).map
                    ((Right.comm
                        M.preimageStructureSheaf
                        ((modulePullbackDerived M.preimageToAmbientOpen).obj
                          ((modulePullbackDerived M.ambientOpenι).obj
                            (pullbackK M K)))).hom ≫
                      tensorRightStructureSheafHom M
                          ((modulePullbackDerived M.preimageToAmbientOpen).obj
                            ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))) ≫
                        etalePullbackHom M K)

private theorem representableEtaleComp {S : Scheme.{u}}
    {T U V : (Over S)ᵒᵖ ⥤ Type u} (f : T ⟶ U) (g : U ⟶ V)
    (hf : Representable.Etale f) (hg : Representable.Etale g) :
    Representable.Etale (f ≫ g) := by
  let hOver : (MorphismProperty.over (@AlgebraicGeometry.Etale) :
      MorphismProperty (Over S)).IsStableUnderComposition :=
    { comp_mem := fun f g hf hg ↦
        @AlgebraicGeometry.Etale.etale_comp _ _ f.left _ g.left hf hg }
  let hPresheaf : Representable.Etale.IsStableUnderComposition :=
    @MorphismProperty.relative_isStableUnderComposition _ _ _ _ yoneda _
      inferInstance inferInstance hOver
  exact @MorphismProperty.comp_mem _ _ Representable.Etale hPresheaf _ _ _ f g hf hg

private theorem ambientOpen_etale (M : DerivedChowPresentation x) : Etale M.ambientOpenι :=
  ⟨fun φ hφ ↦ representableEtaleComp _ _ hφ
    (Representable.isOpenImmersion_etale _
      (Open.inverseImage_isOpenImmersion _ _ M.V.isOpenImmersion.presheaf))⟩

private theorem preimage_etale (M : DerivedChowPresentation x) : Etale M.preimageι :=
  ⟨fun φ hφ ↦ representableEtaleComp _ _ hφ
    (Representable.isOpenImmersion_etale _
      (Open.inverseImage_isOpenImmersion _ _ M.V.isOpenImmersion.presheaf))⟩

private theorem projectiveOpen_etale (M : DerivedChowPresentation x) : Etale M.V.ι :=
  ⟨fun φ hφ ↦ representableEtaleComp _ _ hφ
    (Representable.isOpenImmersion_etale _ M.V.isOpenImmersion.presheaf)⟩

private theorem toOfSchemePullback (M : DerivedChowPresentation x) :
    IsPullback M.ambientOpenι M.ambientOpenTo
      (ProjectiveSpace.toOfScheme M.n X) M.V.ι :=
  ReasLibPullback.isPullback _ _

private theorem immersionPullback (M : DerivedChowPresentation x) :
    IsPullback M.preimageι M.preimageToAmbientOpen M.immersion M.ambientOpenι := by
  apply IsPullback.of_bot (t := toOfSchemePullback M) ?_ (immersion_openCommSq M).w
  have hs : M.preimageToAmbientOpen ≫ M.ambientOpenTo = M.preimageTo :=
    pullback.lift_snd (f := homFunctor (ProjectiveSpace.toOfScheme M.n X))
      (g := homFunctor M.V.ι) _ _ _
  rw [hs]
  exact ReasLibPullback.isPullback M.projectiveProjection M.V.ι

private theorem preimageToAmbientOpen_closed (M : DerivedChowPresentation x) :
    IsClosedImmersion M.preimageToAmbientOpen := by
  have hs : homFunctor M.preimageToAmbientOpen ≫ homFunctor M.ambientOpenTo =
      homFunctor M.preimageTo :=
    pullback.lift_snd (f := homFunctor (ProjectiveSpace.toOfScheme M.n X))
      (g := homFunctor M.V.ι) _ _ _
  have outer := (congrArg (fun k ↦
    IsPullback (C := ((Over (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u))
      (homFunctor M.preimageι) k (homFunctor M.projectiveProjection) (homFunctor M.V.ι)) hs).mpr
        (Open.inverseImage_spec M.projectiveProjection M.V.ι M.V.isOpenImmersion.presheaf).2
  have square := outer.of_bot (immersion_openCommSq M).w
    (Open.inverseImage_spec (ProjectiveSpace.toOfScheme M.n X) M.V.ι
      M.V.isOpenImmersion.presheaf).2
  constructor
  exact (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.over
      (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}))).of_isPullback
        square M.Z.isClosedImmersion.presheaf

private def restrictedStructureIso (M : DerivedChowPresentation x) :
    (modulePullbackDerived M.ambientOpenι).obj M.pushforwardStructureSheaf ≅
      (Modules.moduleDerivedPushforward M.preimageToAmbientOpen).obj M.preimageStructureSheaf :=
  (modulePullbackDerived M.ambientOpenι).mapIso
      ((DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (Modules.pushforward M.immersion)
          (up ℤ) 0).app (SheafOfModules.unit (structureSheaf M.Z.X)))).symm ≪≫
        ModuleDerived.ClosedImmersion.pushforwardCochainIso M.immersion M.Z.isClosedImmersion _) ≪≫
    @Modules.EtaleBaseChangeModel.derivedIso _ _ _ _ _ _ _ _ _
      (ambientOpen_etale M) (preimage_etale M) (immersionPullback M) M.closedStructureSheaf ≪≫
    (Modules.moduleDerivedPushforward M.preimageToAmbientOpen).mapIso
      (@exactPullbackCochainIso _ _ _ _ (preimage_etale M) _ ≪≫
        DerivedCategory.Q.mapIso
          ((HomologicalComplex.singleMapHomologicalComplex (Modules.pullback M.preimageι)
            (up ℤ) 0).app (SheafOfModules.unit (structureSheaf M.Z.X))) ≪≫
        (DerivedCategory.singleFunctor M.preimage.Modules 0).mapIso
          (RelativeProj.pullbackMonoidalUnitIso M.preimageι))

private def etalePullbackIso (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    (modulePullbackDerived M.preimageToAmbientOpen).obj
      ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K)) ≅
      (modulePullbackDerived (M.preimageι ≫ M.sourceProjection)).obj K.obj :=
  (modulePullbackDerived M.preimageToAmbientOpen).mapIso
      ((modulePullbackDerived.compIso M.ambientOpenι (ProjectiveSpace.toBase M.n X)).app K.obj) ≪≫
    (modulePullbackDerived.compIso M.preimageToAmbientOpen
      (M.ambientOpenι ≫ ProjectiveSpace.toBase M.n X)).app K.obj ≪≫
    eqToIso (congrArg (fun f : M.preimage ⟶ X ↦ (modulePullbackDerived f).obj K.obj)
      (congrArg (fun f : M.preimage ⟶ M.ambient ↦ f ≫ ProjectiveSpace.toBase M.n X)
        (pullback.lift_fst (f := homFunctor (ProjectiveSpace.toOfScheme M.n X))
          (g := homFunctor M.V.ι) _ _ _)))

private def restrictionModelIso (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    fourierMukaiRestrict M K ≅ closedImmersionPushforward M K :=
  @Modules.EtaleBaseChangeModel.derivedIso _ _ _ _ _ _ _ _ _
      (projectiveOpen_etale M) (ambientOpen_etale M) (toOfSchemePullback M)
      (tensoredKernel M K) ≪≫
    (Modules.moduleDerivedPushforward M.ambientOpenTo).mapIso
      (@tensorPullbackIso _ _ _ _ (ambientOpen_etale M) (pullbackK M K) M.E ≪≫
        Right.isoApp _ _ ≪≫
        (DerivedTensor.Bifunctor.functor (C := M.ambientOpen.Modules)).mapIso
          ((Iso.refl _).prod
            ((modulePullbackDerived M.ambientOpenι).mapIso (Iso.refl _) ≪≫
              M.restrictionIso ≪≫ restrictedStructureIso M)) ≪≫
        (Right.isoApp _ _).symm ≪≫
        Right.comm _ _ ≪≫
        ModuleDerived.ClosedImmersion.structureProjectionFormulaIso
          M.preimageToAmbientOpen (preimageToAmbientOpen_closed M)
          ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))) ≪≫
    (pushforwardComposition M.preimageToAmbientOpen M.ambientOpenTo).app _ ≪≫
    eqToIso (congrArg (fun f : M.preimage ⟶ M.V.X ↦
      (Modules.moduleDerivedPushforward f).obj
        ((modulePullbackDerived M.preimageToAmbientOpen).obj
          ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))))
      (pullback.lift_snd (f := homFunctor (ProjectiveSpace.toOfScheme M.n X))
        (g := homFunctor M.V.ι) _ _ _)) ≪≫
    (Modules.moduleDerivedPushforward M.preimageTo).mapIso (etalePullbackIso M K)

private def fourierMukaiRestrict_inv (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    closedImmersionPushforward M K ⟶ fourierMukaiRestrict M K :=
  (restrictionModelIso M K).inv

private theorem fourierMukaiRestrict_hom_inv_id (M : DerivedChowPresentation x)
    (K : DerivedQCoh X) :
    fourierMukaiRestrict_hom M K ≫ fourierMukaiRestrict_inv M K = 𝟙 _ := sorry

private theorem fourierMukaiRestrict_inv_hom_id (M : DerivedChowPresentation x)
    (K : DerivedQCoh X) :
    fourierMukaiRestrict_inv M K ≫ fourierMukaiRestrict_hom M K = 𝟙 _ := sorry

/-- Restricting the Fourier–Mukai transform with a derived Chow kernel to the
projective open gives pushforward of the pulled-back complex along its closed immersion. -/
@[stacks 0CTS]
def fourierMukaiRestrict_iso (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    fourierMukaiRestrict M K ≅ closedImmersionPushforward M K where
  hom := fourierMukaiRestrict_hom M K
  inv := fourierMukaiRestrict_inv M K
  hom_inv_id := fourierMukaiRestrict_hom_inv_id M K
  inv_hom_id := fourierMukaiRestrict_inv_hom_id M K

/-- The canonical restriction comparison is invertible. -/
theorem fourierMukaiRestrict_hom_isIso (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    IsIso (fourierMukaiRestrict_hom M K) :=
  (fourierMukaiRestrict_iso M K).isIso_hom

/-- The restriction isomorphism has the canonical Fourier–Mukai comparison as its forward map. -/
theorem fourierMukaiRestrict_iso_hom (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    (fourierMukaiRestrict_iso M K).hom = fourierMukaiRestrict_hom M K := rfl

end AlgebraicGeometry.AlgebraicSpace.DerivedChowPresentation

