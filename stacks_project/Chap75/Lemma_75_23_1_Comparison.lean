/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
public import stacks_project.Chap75.Lemma_75_10_5_Gamma
public import stacks_project.Chap75.Lemma_75_20_1_ProjectionFormula
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Functorial cohomology comparison for a perfect tensor projection formula

Under the standing hypotheses of Lemma 75.22.2, hypercohomology of
`K ⊗ᴸ F` on `B` compares with hypercohomology of `E ⊗ᴸ (G ⊗ f^* F)` on `X`.
The comparison morphism is the composite of the projection-formula mate,
a general-morphism Leray map in `D(Ab)`, and the associator/flat identification
of iterated derived tensor with the underived complex `G ⊗ f^* F`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.Functor
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated ComplexShape TopologicalSpace
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The derived object `K = Rf_*(E ⊗ᴸ Q.obj G)` from the standing notation of
Lemma 75.22.2. -/
def pushforwardTensor (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) : ModuleDerived B :=
  (Modules.pushforwardDerived f).obj
    (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))

/-- `pushforwardTensor` is derived pushforward of the fixed-right derived tensor with
`Q.obj G`. -/
theorem pushforwardTensor_eq (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) :
    pushforwardTensor f E G =
      (Modules.pushforwardDerived f).obj
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G)) :=
  rfl

/-- The underived tensor complex `G ⊗_{𝒪_X} f^* F`, as totalized tensor of `G` with
`f^* F` placed in degree `0`. -/
def complexTensorPullback (f : X ⟶ B) (G : CochainComplex (Modules X) ℤ)
    (F : Modules B) : CochainComplex (Modules X) ℤ :=
  HomologicalComplex.tensorObj G
    ((HomologicalComplex.single (Modules X) (up ℤ) 0).obj ((Modules.pullback f).obj F))

/-- `complexTensorPullback` is totalized tensor of `G` with `f^* F` in degree `0`. -/
theorem complexTensorPullback_obj (f : X ⟶ B) (G : CochainComplex (Modules X) ℤ)
    (F : Modules B) :
    complexTensorPullback f G F =
      HomologicalComplex.tensorObj G
        ((HomologicalComplex.single (Modules X) (up ℤ) 0).obj
          ((Modules.pullback f).obj F)) :=
  rfl

/-- Source object `K ⊗ᴸ F` of the cohomology comparison, with `F` placed in degree `0`. -/
def cohomologySource (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) : ModuleDerived B :=
  DerivedTensor.Right.obj (pushforwardTensor f E G)
    ((DerivedCategory.singleFunctor (Modules B) 0).obj F)

/-- `cohomologySource` is fixed-right derived tensor of `pushforwardTensor` with `F[0]`. -/
theorem cohomologySource_eq (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    cohomologySource f E G F =
      DerivedTensor.Right.obj (pushforwardTensor f E G)
        ((DerivedCategory.singleFunctor (Modules B) 0).obj F) :=
  rfl

/-- Target object `E ⊗ᴸ Q(G ⊗ f^* F)` of the cohomology comparison. -/
def cohomologyTarget (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) : ModuleDerived X :=
  DerivedTensor.Right.obj E (DerivedCategory.Q.obj (complexTensorPullback f G F))

/-- `cohomologyTarget` is fixed-right derived tensor of `E` with `Q.obj (G ⊗ f^* F)`. -/
theorem cohomologyTarget_eq (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    cohomologyTarget f E G F =
      DerivedTensor.Right.obj E (DerivedCategory.Q.obj (complexTensorPullback f G F)) :=
  rfl

/-- Canonical Leray comparison `RΓ(B, Rf_* -) ⟶ RΓ(X, -)` in `D(Ab.{u})` for an
arbitrary morphism of algebraic spaces. -/
def moduleDerivedLerayComparison (f : X ⟶ B) :
    Modules.pushforwardDerived f ⋙ moduleDerivedGlobalSectionsAb B ⟶
      moduleDerivedGlobalSectionsAb X :=
  (Modules.pushforwardDerived f ⋙ moduleDerivedGlobalSectionsAb B).rightDerivedDesc
    (derivedGammaPushforwardCompositeUnit f)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (moduleDerivedGlobalSectionsAb X)
    (whiskerRight (NatTrans.mapHomologicalComplex (gammaPushforwardComparison f) (up ℤ))
        DerivedCategory.Q ≫
      Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsAb X))

/-- `moduleDerivedLerayComparison` is the right-derived descent of the underived
global-sections comparison. -/
theorem moduleDerivedLerayComparison_eq (f : X ⟶ B) :
    moduleDerivedLerayComparison f =
      (Modules.pushforwardDerived f ⋙ moduleDerivedGlobalSectionsAb B).rightDerivedDesc
        (derivedGammaPushforwardCompositeUnit f)
        (HomologicalComplex.quasiIso X.Modules (up ℤ))
        (moduleDerivedGlobalSectionsAb X)
        (whiskerRight (NatTrans.mapHomologicalComplex (gammaPushforwardComparison f) (up ℤ))
            DerivedCategory.Q ≫
          Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsAb X)) :=
  rfl

/-- The general-morphism Leray comparison `RΓ(B, Rf_* -) ⟶ RΓ(X, -)` is an isomorphism. -/
theorem isIso_moduleDerivedLerayComparison (f : X ⟶ B) :
    IsIso (moduleDerivedLerayComparison f) :=
  sorry

/-- Degree-`n` cohomology of the Leray comparison at a derived module on `X`. -/
def moduleDerivedLerayComparison_app (f : X ⟶ B) (W : ModuleDerived X) (n : ℤ) :
    cohomologyAb B ((Modules.pushforwardDerived f).obj W) n ⟶ cohomologyAb X W n :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
    ((moduleDerivedLerayComparison f).app W)

/-- The cochain-level counit `Lf^*(F[0]) ⟶ (f^* F)[0]`. -/
def pullbackDerivedSingleComparison (f : X ⟶ B) (F : Modules B) :
    (modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F) ⟶
      (DerivedCategory.singleFunctor (Modules X) 0).obj ((Modules.pullback f).obj F) :=
  modulePullbackDerived_cochainCounit f
      ((HomologicalComplex.single (Modules B) (up ℤ) 0).obj F) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (Modules.pullback f) (up ℤ) 0).hom.app F)

/-- `pullbackDerivedSingleComparison` is the cochain counit followed by the single-complex
identification of module pullback. -/
theorem pullbackDerivedSingleComparison_eq (f : X ⟶ B) (F : Modules B) :
    pullbackDerivedSingleComparison f F =
      modulePullbackDerived_cochainCounit f
          ((HomologicalComplex.single (Modules B) (up ℤ) 0).obj F) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
              (Modules.pullback f) (up ℤ) 0).hom.app F) :=
  rfl

/-- Homotopy-level underived model `Qh(e ⊗ (G ⊗ K))` of associated derived tensor. -/
def assocUnderivedFunctor (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) :
    HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X :=
  ((curriedTensor (HomotopyCategory (Modules X) (up ℤ))).obj
        ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj G) ⋙
      (curriedTensor (HomotopyCategory (Modules X) (up ℤ))).obj
        ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj
          ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X).objPreimage
            E))) ⋙
    (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X)

/-- Counit of `L ↦ E ⊗ᴸ ((Q G) ⊗ᴸ L)` against `assocUnderivedFunctor`. -/
def assocAssociatedCounit (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) :
    (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X) ⋙
        DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj G) ⋙
          DerivedTensor.Bifunctor.leftFunctor E ⟶
      assocUnderivedFunctor E G where
  app K :=
    (DerivedTensor.Bifunctor.leftFunctor E).map
        ((DerivedTensor.Bifunctor.functor (C := Modules X)).map
            (Prod.mkHom ((DerivedCategory.quotientCompQhIso (Modules X)).inv.app G)
              (𝟙 ((DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤
                ModuleDerived X).obj K))) ≫
          DerivedTensor.Bifunctor.counitApp
              ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj G) K ≫
            (DerivedTensor.Bifunctor.sourceFunctorIsoApp
              ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj G, K)).inv) ≫
      (DerivedTensor.Bifunctor.functor (C := Modules X)).map
          (Prod.mkHom (DerivedTensor.Right.representativeIso E).inv (𝟙 _)) ≫
        DerivedTensor.Bifunctor.counitApp
            ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj
              ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X).objPreimage E))
            (((HomotopyCategory.quotient (Modules X) (up ℤ)).obj G) ⊗ K) ≫
          (DerivedTensor.Bifunctor.sourceFunctorIsoApp
            (((HomotopyCategory.quotient (Modules X) (up ℤ)).obj
                ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X).objPreimage
                  E)),
              ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj G) ⊗ K)).inv
  naturality _ _ _ := sorry

/-- Comparison `E ⊗ᴸ Q G ⟶ Qh(e ⊗ G)` from the two-variable derived-tensor counit. -/
def derivedTensorToHomotopy (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) :
    DerivedTensor.Right.obj E (DerivedCategory.Q.obj G) ⟶
      (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X).obj
        (((HomotopyCategory.quotient (Modules X) (up ℤ)).obj
            ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X).objPreimage E)) ⊗
          ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj G)) :=
  (DerivedTensor.Bifunctor.Right.isoApp (DerivedCategory.Q.obj G) E).hom ≫
    (DerivedTensor.Bifunctor.functor (C := Modules X)).map
      (Prod.mkHom
        ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X).objObjPreimageIso
          E).inv
        ((DerivedCategory.quotientCompQhIso (Modules X)).inv.app G)) ≫
      DerivedTensor.Bifunctor.counitApp
        ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj
          ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X).objPreimage E))
        ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj G) ≫
        (DerivedTensor.Bifunctor.sourceFunctorIsoApp
          (((HomotopyCategory.quotient (Modules X) (up ℤ)).obj
              ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X).objPreimage E)),
            ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj G))).inv

/-- Counit of the iterated functor `L ↦ (E ⊗ᴸ Q G) ⊗ᴸ L` against `assocUnderivedFunctor`. -/
def assocIteratedCounit (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) :
    (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X) ⋙
        DerivedTensor.Bifunctor.leftFunctor
          (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G)) ⟶
      assocUnderivedFunctor E G where
  app K :=
    (DerivedTensor.Bifunctor.functor (C := Modules X)).map
        (Prod.mkHom (derivedTensorToHomotopy E G)
          (𝟙 ((DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤
            ModuleDerived X).obj K))) ≫
      DerivedTensor.Bifunctor.counitApp
          (((HomotopyCategory.quotient (Modules X) (up ℤ)).obj
              ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X).objPreimage
                E)) ⊗
            ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj G)) K ≫
        (DerivedTensor.Bifunctor.sourceFunctorIsoApp
          ((((HomotopyCategory.quotient (Modules X) (up ℤ)).obj
                ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X).objPreimage
                  E)) ⊗
              ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj G)),
            K)).inv ≫
          (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X).map
            (α_ _ _ _).hom
  naturality _ _ _ := sorry

/-- The associated functor `L ↦ E ⊗ᴸ ((Q G) ⊗ᴸ L)` is a left derived functor of
`assocUnderivedFunctor`. -/
instance assocAssociated_isLeftDerived (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) :
    (DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj G) ⋙
          DerivedTensor.Bifunctor.leftFunctor E).IsLeftDerivedFunctor
      (assocAssociatedCounit E G) (HomotopyCategory.quasiIso (Modules X) (up ℤ)) :=
  sorry

/-- Canonical associator `(E ⊗ᴸ Q G) ⊗ᴸ L ⟶ E ⊗ᴸ ((Q G) ⊗ᴸ L)`. -/
def derivedTensorAssoc (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) :
    DerivedTensor.Bifunctor.leftFunctor
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G)) ⟶
      DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj G) ⋙
        DerivedTensor.Bifunctor.leftFunctor E :=
  (DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj G) ⋙
      DerivedTensor.Bifunctor.leftFunctor E).leftDerivedLift
    (assocAssociatedCounit E G) (HomotopyCategory.quasiIso (Modules X) (up ℤ))
    (DerivedTensor.Bifunctor.leftFunctor
      (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G)))
    (assocIteratedCounit E G)

/-- `derivedTensorAssoc` is the left-derived lift of the iterated homotopy counit. -/
theorem derivedTensorAssoc_eq (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) :
    derivedTensorAssoc E G =
      (DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj G) ⋙
          DerivedTensor.Bifunctor.leftFunctor E).leftDerivedLift
        (assocAssociatedCounit E G) (HomotopyCategory.quasiIso (Modules X) (up ℤ))
        (DerivedTensor.Bifunctor.leftFunctor
          (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G)))
        (assocIteratedCounit E G) :=
  rfl

/-- Flat identification `(Q G) ⊗ᴸ (f^* F)[0] ⟶ Q(G ⊗ f^* F)`. -/
def flatTensorComparison (f : X ⟶ B) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    DerivedTensor.Bifunctor.obj (DerivedCategory.Q.obj G)
        ((DerivedCategory.singleFunctor (Modules X) 0).obj ((Modules.pullback f).obj F)) ⟶
      DerivedCategory.Q.obj (complexTensorPullback f G F) :=
  DerivedTensor.Bifunctor.counitAppOfQ G
    ((HomologicalComplex.single (Modules X) (up ℤ) 0).obj ((Modules.pullback f).obj F))

/-- `flatTensorComparison` is the two-variable derived-tensor counit on `G` and `(f^* F)[0]`. -/
theorem flatTensorComparison_eq (f : X ⟶ B) (G : CochainComplex (Modules X) ℤ)
    (F : Modules B) :
    flatTensorComparison f G F =
      DerivedTensor.Bifunctor.counitAppOfQ G
        ((HomologicalComplex.single (Modules X) (up ℤ) 0).obj
          ((Modules.pullback f).obj F)) :=
  rfl

/-- Canonical identification `(E ⊗ᴸ G) ⊗ᴸ Lf^* F ⟶ E ⊗ᴸ Q(G ⊗ f^* F)`. -/
def tensorPullbackIdentification (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    DerivedTensor.Right.obj
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))
        ((modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) ⟶
      cohomologyTarget f E G F :=
  (DerivedTensor.Bifunctor.Right.isoApp
        ((modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F))
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor
          (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))).map
        (pullbackDerivedSingleComparison f F) ≫
      (derivedTensorAssoc E G).app
          ((DerivedCategory.singleFunctor (Modules X) 0).obj ((Modules.pullback f).obj F)) ≫
        (DerivedTensor.Bifunctor.leftFunctor E).map (flatTensorComparison f G F) ≫
          (DerivedTensor.Bifunctor.Right.isoApp
              (DerivedCategory.Q.obj (complexTensorPullback f G F)) E).inv

/-- `tensorPullbackIdentification` is pullback-counit, associator, then flat identification. -/
theorem tensorPullbackIdentification_eq (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    tensorPullbackIdentification f E G F =
      (DerivedTensor.Bifunctor.Right.isoApp
            ((modulePullbackDerived f).obj
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F))
            (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))).hom ≫
        (DerivedTensor.Bifunctor.leftFunctor
              (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))).map
            (pullbackDerivedSingleComparison f F) ≫
          (derivedTensorAssoc E G).app
              ((DerivedCategory.singleFunctor (Modules X) 0).obj
                ((Modules.pullback f).obj F)) ≫
            (DerivedTensor.Bifunctor.leftFunctor E).map (flatTensorComparison f G F) ≫
              (DerivedTensor.Bifunctor.Right.isoApp
                  (DerivedCategory.Q.obj (complexTensorPullback f G F)) E).inv :=
  rfl

/-- The intermediate object `Rf_*((E ⊗ᴸ G) ⊗ᴸ Lf^* F)` appearing after the projection-formula
mate. -/
def cohomologyIntermediate (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) : ModuleDerived B :=
  (Modules.pushforwardDerived f).obj
    (DerivedTensor.Right.obj (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))
      ((modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F)))

/-- Functorial comparison `H^i(B, K ⊗ᴸ F) ⟶ H^i(X, E ⊗ᴸ (G ⊗ f^* F))`. -/
def cohomologyComparison (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) (i : ℤ) :
    cohomologyAb B (cohomologySource f E G F) i ⟶
      cohomologyAb X (cohomologyTarget f E G F) i :=
  cohomologyAb_map
      (leftMate f (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))
        ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ≫
    moduleDerivedLerayComparison_app f
      (DerivedTensor.Right.obj (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))
        ((modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F)))
      i ≫
      cohomologyAb_map (tensorPullbackIdentification f E G F) i

/-- `cohomologyComparison` is cohomology of `leftMate`, then Leray, then the
associator/flat identification. -/
theorem cohomologyComparison_eq (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) (i : ℤ) :
    cohomologyComparison f E G F i =
      cohomologyAb_map
          (leftMate f (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))
            ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ≫
        moduleDerivedLerayComparison_app f
          (DerivedTensor.Right.obj (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))
            ((modulePullbackDerived f).obj
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F))) i ≫
          cohomologyAb_map (tensorPullbackIdentification f E G F) i :=
  rfl

variable (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]

/-- The comparison `H^i(B, K ⊗ᴸ F) ⟶ H^i(X, E ⊗ᴸ (G ⊗ f^* F))` is an isomorphism. -/
theorem cohomologyComparison_isIso (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i))))
    (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ) :
    IsIso (cohomologyComparison f E G F i) :=
  sorry

/-- Induced map on `K ⊗ᴸ -` from a morphism of quasi-coherent modules on `B`. -/
def cohomologySourceMap (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ)
    {F F' : Modules B} (φ : F ⟶ F') :
    cohomologySource f E G F ⟶ cohomologySource f E G F' :=
  (DerivedTensor.Bifunctor.Right.isoApp
        ((DerivedCategory.singleFunctor (Modules B) 0).obj F)
        (pushforwardTensor f E G)).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor (pushforwardTensor f E G)).map
      ((DerivedCategory.singleFunctor (Modules B) 0).map φ) ≫
      (DerivedTensor.Bifunctor.Right.isoApp
          ((DerivedCategory.singleFunctor (Modules B) 0).obj F')
          (pushforwardTensor f E G)).inv

/-- Induced map on `E ⊗ᴸ Q(G ⊗ f^* -)` from a morphism of modules on `B`. -/
def cohomologyTargetMap (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ)
    {F F' : Modules B} (φ : F ⟶ F') :
    cohomologyTarget f E G F ⟶ cohomologyTarget f E G F' :=
  (DerivedTensor.Bifunctor.Right.isoApp
        (DerivedCategory.Q.obj (complexTensorPullback f G F)) E).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor E).map
      (DerivedCategory.Q.map
        (HomologicalComplex.tensorHom (𝟙 G)
          ((HomologicalComplex.single (Modules X) (up ℤ) 0).map
            ((Modules.pullback f).map φ)))) ≫
      (DerivedTensor.Bifunctor.Right.isoApp
          (DerivedCategory.Q.obj (complexTensorPullback f G F')) E).inv

/-- The cohomology comparison is natural in the quasi-coherent module `F`. -/
theorem cohomologyComparison_naturality (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i))))
    {F F' : Modules B} (φ : F ⟶ F')
    (hF : quasiCoherentModuleProperty B F) (hF' : quasiCoherentModuleProperty B F') (i : ℤ) :
    cohomologyComparison f E G F i ≫ cohomologyAb_map (cohomologyTargetMap f E G φ) i =
      cohomologyAb_map (cohomologySourceMap f E G φ) i ≫ cohomologyComparison f E G F' i :=
  sorry

/-- Termwise tensor of `G` against `f^*` of a short complex of modules on `B`. -/
def complexTensorPullbackShortComplex (G : CochainComplex (Modules X) ℤ)
    (s : ShortComplex (Modules B)) : ShortComplex (CochainComplex (Modules X) ℤ) :=
  ShortComplex.mk
    (HomologicalComplex.tensorHom (𝟙 G)
      ((HomologicalComplex.single (Modules X) (up ℤ) 0).map ((Modules.pullback f).map s.f)))
    (HomologicalComplex.tensorHom (𝟙 G)
      ((HomologicalComplex.single (Modules X) (up ℤ) 0).map ((Modules.pullback f).map s.g)))
    sorry

/-- The short complex `G ⊗ f^* s` is exact when `s` is exact and each `G^n` is flat over `B`. -/
theorem complexTensorPullback_shortExact (G : CochainComplex (Modules X) ℤ)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x) (s : ShortComplex (Modules B))
    (hs : s.ShortExact) : (complexTensorPullbackShortComplex f G s).ShortExact :=
  sorry

/-- Connecting map on `H^i(B, K ⊗ᴸ -)` attached to a short exact sequence of modules on `B`. -/
def cohomologySourceδ (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ)
    (s : ShortComplex (Modules B))
    (hs : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact) (i : ℤ) :
    cohomologyAb B (cohomologySource f E G s.X₃) i ⟶
      cohomologyAb B (cohomologySource f E G s.X₁) (i + 1) :=
  cohomologyAb_map
      (DerivedTensor.Bifunctor.Right.comm (pushforwardTensor f E G)
        ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₃)).hom i ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
      ((moduleDerivedGlobalSectionsAb B).mapTriangle.obj
        ((DerivedTensor.Right.functor (pushforwardTensor f E G)).mapTriangle.obj
          (DerivedCategory.triangleOfSES hs)))
      i (i + 1) rfl ≫
      cohomologyAb_map
        (DerivedTensor.Bifunctor.Right.comm (pushforwardTensor f E G)
          ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₁)).inv (i + 1)

/-- Connecting map on `H^i(X, E ⊗ᴸ (G ⊗ f^* -))` attached to a short exact sequence of
modules on `B`. -/
def cohomologyTargetδ (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ)
    (s : ShortComplex (Modules B))
    (hs : (complexTensorPullbackShortComplex f G s).ShortExact) (i : ℤ) :
    cohomologyAb X (cohomologyTarget f E G s.X₃) i ⟶
      cohomologyAb X (cohomologyTarget f E G s.X₁) (i + 1) :=
  cohomologyAb_map
      (DerivedTensor.Bifunctor.Right.comm E
        (DerivedCategory.Q.obj (complexTensorPullback f G s.X₃))).hom i ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
      ((moduleDerivedGlobalSectionsAb X).mapTriangle.obj
        ((DerivedTensor.Right.functor E).mapTriangle.obj (DerivedCategory.triangleOfSES hs)))
      i (i + 1) rfl ≫
      cohomologyAb_map
        (DerivedTensor.Bifunctor.Right.comm E
          (DerivedCategory.Q.obj (complexTensorPullback f G s.X₁))).inv (i + 1)

/-- The cohomology comparison commutes with connecting maps of a short exact sequence of
quasi-coherent modules on `B`. -/
theorem cohomologyComparison_boundary (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i))))
    (s : ShortComplex (Modules B)) (hs : s.ShortExact)
    (hs0 : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
    (hF₁ : quasiCoherentModuleProperty B s.X₁)
    (hF₂ : quasiCoherentModuleProperty B s.X₂)
    (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ) :
    cohomologyComparison f E G s.X₃ i ≫
        cohomologyTargetδ f E G s (complexTensorPullback_shortExact f G hG_flat s hs) i =
      cohomologySourceδ f E G s hs0 i ≫ cohomologyComparison f E G s.X₁ (i + 1) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
