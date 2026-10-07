module

public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_5_6_Tensor
public import stacks_project.Chap75.Lemma_75_20_1_ProjectionFormula
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange
public import stacks_project.Chap75.Lemma_75_23_1_Comparison
public import stacks_project.Chap75.Remark_75_20_6_Counit
public import stacks_project.Chap76.Lemma_76_51_2_Derived_Chow_s_lemma_Presentation

/-!
# Restriction of the derived Fourier–Mukai complex of a derived Chow presentation

In the setup of derived Chow's lemma, restriction to the chosen open `V ⊂ ℙⁿ_A`
identifies `Rq_*(Lp^* K ⊗^L E)` with the pushforward of `K|_W` along the finitely
presented closed immersion `W ⟶ V`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.DerivedCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory ComplexShape
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Hom
open DerivedTensor.Bifunctor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedChowPresentation

/-- Explicit-cospan lift in the functor-of-points category. -/
def functorOfPointsLift {S : Scheme.{u}} {W X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : W ⟶ pullback f g :=
  pullback.lift h k w

/-- First projection identity for `functorOfPointsLift`. -/
theorem functorOfPointsLift_fst {S : Scheme.{u}} {W X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    functorOfPointsLift f g h k w ≫ pullback.fst f g = h :=
  pullback.lift_fst h k w

/-- Second projection identity for `functorOfPointsLift`. -/
theorem functorOfPointsLift_snd {S : Scheme.{u}} {W X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    functorOfPointsLift f g h k w ≫ pullback.snd f g = k :=
  pullback.lift_snd h k w

/-- Explicit-cospan form of the functor-of-points pullback condition. -/
theorem functorOfPoints_condition {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g :=
  pullback.condition

variable {A : Type u} [CommRing A]
  {X : AlgebraicSpace (Spec (CommRingCat.of A))}
  [Separated (toBase X)] [FinitePresentation (toBase X)]
  {x : Points X}

/-- Restriction to `V` of `Rq_*(Lp^* K ⊗^L E)`, for the projections
`p = ProjectiveSpace.toBase M.n X` and `q = ProjectiveSpace.toOfScheme M.n X`. -/
noncomputable def fourierMukaiRestrict (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    ModuleDerived M.V.X :=
  let pullbackK := (modulePullbackDerived (ProjectiveSpace.toBase M.n X)).obj K.obj
  let tensored := (DerivedTensor.Right.functor M.E).obj pullbackK
  let pushed := (Modules.pushforwardDerived (ProjectiveSpace.toOfScheme M.n X)).obj tensored
  (modulePullbackDerived M.V.ι).obj pushed

/-- `fourierMukaiRestrict` is the functor composite
`modulePullbackDerived p ⋙ DerivedTensor.Right.functor E ⋙
Modules.pushforwardDerived q ⋙ modulePullbackDerived V.ι`. -/
theorem fourierMukaiRestrict_eq (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    fourierMukaiRestrict M K =
      (modulePullbackDerived (ProjectiveSpace.toBase M.n X) ⋙
          DerivedTensor.Right.functor M.E ⋙
          Modules.pushforwardDerived (ProjectiveSpace.toOfScheme M.n X) ⋙
          modulePullbackDerived M.V.ι).obj
        K.obj := sorry

/-- Pushforward of `K|_W` along `W ⟶ V = M.preimageTo`, where restriction to `W`
is derived pullback along `M.preimageι ≫ M.sourceProjection`. -/
noncomputable def closedImmersionPushforward (M : DerivedChowPresentation x)
    (K : DerivedQCoh X) : ModuleDerived M.V.X :=
  let restrictK :=
    (modulePullbackDerived (M.preimageι ≫ M.sourceProjection)).obj K.obj
  (Modules.pushforwardDerived M.preimageTo).obj restrictK

/-- `closedImmersionPushforward` is the functor composite
`modulePullbackDerived (W ⟶ X) ⋙ Modules.pushforwardDerived (W ⟶ V)`. -/
theorem closedImmersionPushforward_eq (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    closedImmersionPushforward M K =
      (modulePullbackDerived (M.preimageι ≫ M.sourceProjection) ⋙
          Modules.pushforwardDerived M.preimageTo).obj
        K.obj := sorry

/-- The comparison `W ⟶ V = c|_W` of a derived Chow presentation is of finite
presentation. -/
instance finitePresentation_preimageTo (M : DerivedChowPresentation x) :
    FinitePresentation M.preimageTo := sorry

/-- The projection `q' : X ×_A V ⟶ V` of a derived Chow presentation. -/
def ambientOpenTo (M : DerivedChowPresentation x) : M.ambientOpen ⟶ M.V.X :=
  openInverseImageTo (ProjectiveSpace.toOfScheme M.n X) M.V.ι

/-- The cartesian square of `q = ProjectiveSpace.toOfScheme M.n X` along `M.V.ι`. -/
theorem toOfScheme_openCommSq (M : DerivedChowPresentation x) :
    CommSq M.ambientOpenι M.ambientOpenTo
      (ProjectiveSpace.toOfScheme M.n X) M.V.ι :=
  ⟨functorOfPoints_condition
      (toFunctorOfPoints (ProjectiveSpace.toOfScheme M.n X))
      (toFunctorOfPoints M.V.ι)⟩

/-- Derived pullback along `q' ≫ V.ι` agrees with the iterated pullback. -/
instance instIsIso_compComparison_ambientOpenTo (M : DerivedChowPresentation x) :
    IsIso (modulePullbackDerived.compComparison M.ambientOpenTo M.V.ι) :=
  sorry

/-- Derived pullback along `ambientOpenι ≫ q` agrees with the iterated pullback. -/
instance instIsIso_compComparison_ambientOpenι (M : DerivedChowPresentation x) :
    IsIso (modulePullbackDerived.compComparison M.ambientOpenι
      (ProjectiveSpace.toOfScheme M.n X)) :=
  sorry

/-- The cone of `W ⟶ X ×_A ℙⁿ_A` and `W ⟶ V` commutes over `ℙⁿ_A`. -/
theorem preimageToAmbientOpen_w (M : DerivedChowPresentation x) :
    (M.preimageι ≫ M.immersion) ≫
        toFunctorOfPoints (ProjectiveSpace.toOfScheme M.n X) =
      M.preimageTo ≫ toFunctorOfPoints M.V.ι :=
  functorOfPoints_condition
    (toFunctorOfPoints M.projectiveProjection)
    (toFunctorOfPoints M.V.ι)

/-- The closed immersion `i : W ⟶ X ×_A V` over `V`. -/
def preimageToAmbientOpen (M : DerivedChowPresentation x) : M.preimage ⟶ M.ambientOpen :=
  (functorOfPointsLift
      (toFunctorOfPoints (ProjectiveSpace.toOfScheme M.n X))
      (toFunctorOfPoints M.V.ι)
      (M.preimageι ≫ M.immersion)
      M.preimageTo
      (preimageToAmbientOpen_w M) :
    M.preimage.functorOfPoints ⟶ M.ambientOpen.functorOfPoints)

/-- Derived pullback along `i ≫ ambientOpenι` agrees with the iterated pullback. -/
instance instIsIso_compComparison_preimageToAmbientOpen_ι (M : DerivedChowPresentation x) :
    IsIso (modulePullbackDerived.compComparison M.preimageToAmbientOpen M.ambientOpenι) :=
  sorry

/-- Derived pullback along `preimageι ≫ Z.ι` agrees with the iterated pullback. -/
instance instIsIso_compComparison_preimageι_immersion (M : DerivedChowPresentation x) :
    IsIso (modulePullbackDerived.compComparison M.preimageι M.immersion) :=
  sorry

/-- Derived pullback along `i ≫ q'` agrees with the iterated pullback. -/
instance instIsIso_compComparison_preimageToAmbientOpen_to (M : DerivedChowPresentation x) :
    IsIso (modulePullbackDerived.compComparison M.preimageToAmbientOpen M.ambientOpenTo) :=
  sorry

/-- The cartesian square of the closed immersion `Z ⟶ X ×_A ℙⁿ_A` along `X ×_A V`. -/
theorem immersion_openCommSq (M : DerivedChowPresentation x) :
    CommSq M.preimageι M.preimageToAmbientOpen M.immersion M.ambientOpenι :=
  ⟨(functorOfPointsLift_fst
      (toFunctorOfPoints (ProjectiveSpace.toOfScheme M.n X))
      (toFunctorOfPoints M.V.ι)
      (M.preimageι ≫ M.immersion) M.preimageTo
      (preimageToAmbientOpen_w M)).symm⟩

/-- `Lp^* K` on the ambient fibre product. -/
def pullbackK (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    ModuleDerived M.ambient :=
  (modulePullbackDerived (ProjectiveSpace.toBase M.n X)).obj K.obj

/-- `Lp^* K ⊗^L E` on the ambient fibre product. -/
def tensoredKernel (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    ModuleDerived M.ambient :=
  (DerivedTensor.Right.functor M.E).obj (pullbackK M K)

/-- Degree-zero structure sheaf of `W`. -/
def preimageStructureSheaf (M : DerivedChowPresentation x) : ModuleDerived M.preimage :=
  (DerivedCategory.singleFunctor (Modules M.preimage) 0).obj
    (SheafOfModules.unit (structureSheaf M.preimage))

/-- Degree-zero structure sheaf of `Z`. -/
def closedStructureSheaf (M : DerivedChowPresentation x) : ModuleDerived M.Z.X :=
  (DerivedCategory.singleFunctor (Modules M.Z.X) 0).obj
    (SheafOfModules.unit (structureSheaf M.Z.X))

/-- Replace `E|_{X ×_A V}` by the pushforward of `𝒪_Z` inside the restricted tensor. -/
def restrictionReplaceHom (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
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
def underivedToDerivedPushforward (M : DerivedChowPresentation x) :
    M.pushforwardStructureSheaf ⟶
      (Modules.pushforwardDerived M.immersion).obj M.closedStructureSheaf :=
  DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
          (Modules.pushforward M.immersion) (up ℤ) 0).inv.app
        (SheafOfModules.unit (structureSheaf M.Z.X))) ≫
    (Modules.moduleDerivedPushforward.unit M.immersion).app
      ((HomologicalComplex.single (Modules M.Z.X) (up ℤ) 0).obj
        (SheafOfModules.unit (structureSheaf M.Z.X)))

/-- Identify `(b, c)_* 𝒪_Z` restricted to `X ×_A V` with `Ri_* 𝒪_W`. -/
def restrictedStructureToPushforward (M : DerivedChowPresentation x) :
    (modulePullbackDerived M.ambientOpenι).obj M.pushforwardStructureSheaf ⟶
      (Modules.pushforwardDerived M.preimageToAmbientOpen).obj M.preimageStructureSheaf :=
  (modulePullbackDerived M.ambientOpenι).map (underivedToDerivedPushforward M) ≫
    Hom.DerivedBaseChange.app (immersion_openCommSq M) M.closedStructureSheaf ≫
      (Modules.pushforwardDerived M.preimageToAmbientOpen).map
        (ModuleDerived.pullbackDerivedSingleComparison M.preimageι
            (SheafOfModules.unit (structureSheaf M.Z.X)) ≫
          (DerivedCategory.singleFunctor (Modules M.preimage) 0).map
            (IdealSubobject.pullbackUnit M.preimageι))

/-- Apply the projection-formula mate along `i : W ⟶ X ×_A V`. -/
def projectionFormulaHom (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    (DerivedTensor.Right.functor
        ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))).obj
      ((Modules.pushforwardDerived M.preimageToAmbientOpen).obj M.preimageStructureSheaf) ⟶
      (Modules.pushforwardDerived M.preimageToAmbientOpen).obj
        ((DerivedTensor.Right.functor
            ((modulePullbackDerived M.preimageToAmbientOpen).obj
              ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K)))).obj
          M.preimageStructureSheaf) :=
  leftMate M.preimageToAmbientOpen M.preimageStructureSheaf
    ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))

/-- Identify `Li^* Lp^* K|_{X ×_A V}` with `K|_W`. -/
def etalePullbackHom (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
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
            (functorOfPointsLift_fst
              (toFunctorOfPoints (ProjectiveSpace.toOfScheme M.n X))
              (toFunctorOfPoints M.V.ι)
              (M.preimageι ≫ M.immersion) M.preimageTo
              (preimageToAmbientOpen_w M))))

/-- The structure sheaf is the monoidal unit of `𝒪_W`-modules. -/
def preimageStructureModuleUnitIso (M : DerivedChowPresentation x) :
    SheafOfModules.unit (structureSheaf M.preimage) ≅ 𝟙_ (Modules M.preimage) :=
  Modules.structureModuleIsoTensorUnit M.preimage

/-- The degree-zero monoidal unit complex is the monoidal unit of cochain complexes. -/
def preimageUnitComplexIso (M : DerivedChowPresentation x) :
    ((HomologicalComplex.single (Modules M.preimage) (up ℤ) 0).obj
        (𝟙_ (Modules M.preimage))) ≅
      𝟙_ (CochainComplex (Modules M.preimage) ℤ) :=
  Iso.refl _

/-- Drop derived tensoring with `𝒪_W[0]` via the two-variable counit and the underived
right unitor. -/
def tensorRightStructureSheafHom (M : DerivedChowPresentation x)
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
    (Modules.pushforwardDerived M.ambientOpenTo).map (restrictionReplaceHom M K) ≫
      (Modules.pushforwardDerived M.ambientOpenTo).map
          ((Right.isoApp
                ((modulePullbackDerived M.ambientOpenι).obj M.pushforwardStructureSheaf)
                ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))).hom ≫
            tensorBifunctor.map
                (Prod.mkHom
                  (𝟙 ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K)))
                  (restrictedStructureToPushforward M)) ≫
              (Right.isoApp
                  ((Modules.pushforwardDerived M.preimageToAmbientOpen).obj
                    M.preimageStructureSheaf)
                  ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))).inv) ≫
        (Modules.pushforwardDerived M.ambientOpenTo).map
            (Right.comm
              ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))
              ((Modules.pushforwardDerived M.preimageToAmbientOpen).obj
                M.preimageStructureSheaf)).hom ≫
          (Modules.pushforwardDerived M.ambientOpenTo).map (projectionFormulaHom M K) ≫
            (Modules.pushforwardDerived.compIso M.preimageToAmbientOpen M.ambientOpenTo).hom.app
                ((DerivedTensor.Right.functor
                    ((modulePullbackDerived M.preimageToAmbientOpen).obj
                      ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K)))).obj
                  M.preimageStructureSheaf) ≫
              eqToHom
                  (congrArg
                    (fun f : M.preimage ⟶ M.V.X ↦
                      (Modules.pushforwardDerived f).obj
                        ((DerivedTensor.Right.functor
                            ((modulePullbackDerived M.preimageToAmbientOpen).obj
                              ((modulePullbackDerived M.ambientOpenι).obj
                                (pullbackK M K)))).obj
                          M.preimageStructureSheaf))
                    (functorOfPointsLift_snd
                      (toFunctorOfPoints (ProjectiveSpace.toOfScheme M.n X))
                      (toFunctorOfPoints M.V.ι)
                      (M.preimageι ≫ M.immersion) M.preimageTo
                      (preimageToAmbientOpen_w M))) ≫
                (Modules.pushforwardDerived M.preimageTo).map
                    ((Right.comm
                        M.preimageStructureSheaf
                        ((modulePullbackDerived M.preimageToAmbientOpen).obj
                          ((modulePullbackDerived M.ambientOpenι).obj
                            (pullbackK M K)))).hom ≫
                      tensorRightStructureSheafHom M
                          ((modulePullbackDerived M.preimageToAmbientOpen).obj
                            ((modulePullbackDerived M.ambientOpenι).obj (pullbackK M K))) ≫
                        etalePullbackHom M K)

/-- The Fourier–Mukai restriction comparison is an isomorphism. -/
instance fourierMukaiRestrict_hom_isIso (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    IsIso (fourierMukaiRestrict_hom M K) :=
  sorry

/-- Lemma 76.51.3. Let `X` over `A`, `x ∈ Points X`, and `n`, `Z`, `z`, `V`, `E`
be as in Lemma 76.51.2. For any `K` in `DerivedQCoh X` there is a canonical
identification `fourierMukaiRestrict M K ≅ closedImmersionPushforward M K`
in `ModuleDerived V.X`, where `p = ProjectiveSpace.toBase M.n X` and
`q = ProjectiveSpace.toOfScheme M.n X` are the projections and `W ⟶ V` is the
finitely presented closed immersion `c|_W = M.preimageTo`. -/
@[stacks 0CTS]
noncomputable def fourierMukaiRestrict_iso (M : DerivedChowPresentation x)
    (K : DerivedQCoh X) :
    fourierMukaiRestrict M K ≅ closedImmersionPushforward M K :=
  asIso (fourierMukaiRestrict_hom M K)

/-- The forward map of `fourierMukaiRestrict_iso` is `fourierMukaiRestrict_hom`. -/
theorem fourierMukaiRestrict_iso_hom (M : DerivedChowPresentation x) (K : DerivedQCoh X) :
    (fourierMukaiRestrict_iso M K).hom = fourierMukaiRestrict_hom M K :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.DerivedChowPresentation
