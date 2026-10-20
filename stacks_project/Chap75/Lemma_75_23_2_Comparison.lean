/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import stacks_project.Chap75.Lemma_75_23_1_Comparison

/-!
# Functorial Ext comparison for a perfect internal-Hom projection formula

Under the standing hypotheses of Lemma 75.22.3, hypercohomology of
`K ⊗ᴸ F` on `B` compares with hypercohomology of `RHom(E, G ⊗ f^* F)` on `X`.
The comparison morphism is the composite of the projection-formula mate,
a general-morphism Leray map in `D(Ab)`, and the tensor/internal-Hom
identification of `ihom(E, Q G) ⊗ᴸ Lf^* F` with `ihom(E, Q(G ⊗ f^* F))`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.Functor
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.Pretriangulated
open ComplexShape TopologicalSpace
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)]

/-- The derived object `K = Rf_*(ihom(E, Q G))` from the standing notation of
Lemma 75.22.3. -/
def pushforwardInternalHom (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) : ModuleDerived B :=
  (Modules.pushforwardDerived f).obj
    ((ihomOf H E).obj (DerivedCategory.Q.obj G))

/-- `pushforwardInternalHom` is derived pushforward of the derived internal Hom into `Q.obj G`. -/
theorem pushforwardInternalHom_eq (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) :
    pushforwardInternalHom f H E G =
      (Modules.pushforwardDerived f).obj
        ((ihomOf H E).obj (DerivedCategory.Q.obj G)) :=
  rfl

/-- Source object `K ⊗ᴸ F` of the Ext comparison, with `F` placed in degree `0`. -/
def extSource (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    ModuleDerived B :=
  DerivedTensor.Right.obj (pushforwardInternalHom f H E G)
    ((DerivedCategory.singleFunctor (Modules B) 0).obj F)

/-- `extSource` is fixed-right derived tensor of `pushforwardInternalHom` with `F[0]`. -/
theorem extSource_eq (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    extSource f H E G F =
      DerivedTensor.Right.obj (pushforwardInternalHom f H E G)
        ((DerivedCategory.singleFunctor (Modules B) 0).obj F) :=
  rfl

/-- Target object `ihom(E, Q(G ⊗ f^* F))`, the derived internal-Hom model of
`Ext^i_{𝒪_X}(E, G ⊗ f^* F)`. -/
def extTarget (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    ModuleDerived X :=
  (ihomOf H E).obj (DerivedCategory.Q.obj (complexTensorPullback f G F))

/-- `extTarget` is the derived internal Hom from `E` into `Q.obj (G ⊗ f^* F)`. -/
theorem extTarget_eq (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    extTarget f H E G F =
      (ihomOf H E).obj (DerivedCategory.Q.obj (complexTensorPullback f G F)) :=
  rfl

/-- Identification `(ihom E A) ⊗ B ⟶ ihom E (A ⊗ B)` obtained by currying evaluation
against the tensor-left adjunction of an explicit closed owner. -/
def ihomTensorRightComparison (H : MonoidalClosed (ModuleDerived X))
    (E A B : ModuleDerived X) :
    (ihomOf H E).obj A ⊗ B ⟶ (ihomOf H E).obj (A ⊗ B) :=
  (adjunctionOf H E).homEquiv ((ihomOf H E).obj A ⊗ B) (A ⊗ B)
    ((α_ E ((ihomOf H E).obj A) B).inv ≫ ((adjunctionOf H E).counit.app A ▷ B))

/-- `ihomTensorRightComparison` is the curry of reassociation followed by evaluation. -/
theorem ihomTensorRightComparison_eq (H : MonoidalClosed (ModuleDerived X))
    (E A B : ModuleDerived X) :
    ihomTensorRightComparison H E A B =
      (adjunctionOf H E).homEquiv ((ihomOf H E).obj A ⊗ B) (A ⊗ B)
        ((α_ E ((ihomOf H E).obj A) B).inv ≫
          ((adjunctionOf H E).counit.app A ▷ B)) :=
  rfl

/-- Strong monoidality of the homotopy localization of `D(𝒪_Y)`, used to compare
fixed-right derived tensor with the ambient monoidal tensor on `ModuleDerived Y`. -/
abbrev localizationMonoidal (Y : AlgebraicSpace S)
    [MonoidalCategory (ModuleDerived Y)] :=
  (DerivedTensor.Right.localization :
    HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y).Monoidal

variable [localizationMonoidal X]

/-- Canonical identification `(ihom(E, Q G)) ⊗ᴸ Lf^* F ⟶ ihom(E, Q(G ⊗ f^* F))`. -/
def ihomTensorPullbackIdentification (f : X ⟶ B)
    (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    DerivedTensor.Right.obj
        ((ihomOf H E).obj (DerivedCategory.Q.obj G))
        ((modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) ⟶
      extTarget f H E G F :=
  (DerivedTensor.Right.Monoidal.Strong.objIsoTensor
        ((ihomOf H E).obj (DerivedCategory.Q.obj G))
        ((modulePullbackDerived f).obj
          ((DerivedCategory.singleFunctor (Modules B) 0).obj F))).hom ≫
    (tensorLeft ((ihomOf H E).obj (DerivedCategory.Q.obj G))).map
        (pullbackDerivedSingleComparison f F) ≫
      ihomTensorRightComparison H E (DerivedCategory.Q.obj G)
          ((DerivedCategory.singleFunctor (Modules X) 0).obj
            ((Modules.pullback f).obj F)) ≫
        (ihomOf H E).map
          ((DerivedTensor.Right.Monoidal.Strong.objIsoTensor
                (DerivedCategory.Q.obj G)
                ((DerivedCategory.singleFunctor (Modules X) 0).obj
                  ((Modules.pullback f).obj F))).inv ≫
            (DerivedTensor.Bifunctor.Right.isoApp
                ((DerivedCategory.singleFunctor (Modules X) 0).obj
                  ((Modules.pullback f).obj F))
                (DerivedCategory.Q.obj G)).hom ≫
              flatTensorComparison f G F)

/-- `ihomTensorPullbackIdentification` is the ambient-tensor comparison, pullback-counit,
tensor/internal-Hom comparison, then flat identification. -/
theorem ihomTensorPullbackIdentification_eq (f : X ⟶ B)
    (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    ihomTensorPullbackIdentification f H E G F =
      (DerivedTensor.Right.Monoidal.Strong.objIsoTensor
            ((ihomOf H E).obj (DerivedCategory.Q.obj G))
            ((modulePullbackDerived f).obj
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F))).hom ≫
        (tensorLeft ((ihomOf H E).obj (DerivedCategory.Q.obj G))).map
            (pullbackDerivedSingleComparison f F) ≫
          ihomTensorRightComparison H E (DerivedCategory.Q.obj G)
              ((DerivedCategory.singleFunctor (Modules X) 0).obj
                ((Modules.pullback f).obj F)) ≫
            (ihomOf H E).map
              ((DerivedTensor.Right.Monoidal.Strong.objIsoTensor
                    (DerivedCategory.Q.obj G)
                    ((DerivedCategory.singleFunctor (Modules X) 0).obj
                      ((Modules.pullback f).obj F))).inv ≫
                (DerivedTensor.Bifunctor.Right.isoApp
                    ((DerivedCategory.singleFunctor (Modules X) 0).obj
                      ((Modules.pullback f).obj F))
                    (DerivedCategory.Q.obj G)).hom ≫
                  flatTensorComparison f G F) :=
  rfl

/-- Functorial comparison `H^i(B, K ⊗ᴸ F) ⟶ H^i(X, RHom(E, G ⊗ f^* F))`. -/
def extComparison (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) (i : ℤ) :
    cohomologyAb B (extSource f H E G F) i ⟶ cohomologyAb X (extTarget f H E G F) i :=
  cohomologyAb_map
      (leftMate f ((ihomOf H E).obj (DerivedCategory.Q.obj G))
        ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ≫
    moduleDerivedLerayComparison_app f
      (DerivedTensor.Right.obj ((ihomOf H E).obj (DerivedCategory.Q.obj G))
        ((modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F)))
      i ≫
      cohomologyAb_map (ihomTensorPullbackIdentification f H E G F) i

/-- `extComparison` is cohomology of `leftMate`, then Leray, then the
tensor/internal-Hom identification. -/
theorem extComparison_eq (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) (i : ℤ) :
    extComparison f H E G F i =
      cohomologyAb_map
          (leftMate f ((ihomOf H E).obj (DerivedCategory.Q.obj G))
            ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ≫
        moduleDerivedLerayComparison_app f
          (DerivedTensor.Right.obj ((ihomOf H E).obj (DerivedCategory.Q.obj G))
            ((modulePullbackDerived f).obj
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F))) i ≫
          cohomologyAb_map (ihomTensorPullbackIdentification f H E G F) i :=
  rfl

variable (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]

/-- The comparison `H^i(B, K ⊗ᴸ F) ⟶ Ext^i_{𝒪_X}(E, G ⊗ f^* F)` is an isomorphism. -/
theorem extComparison_isIso (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i))))
    (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ) :
    IsIso (extComparison f H E G F i) :=
  sorry

/-- Induced map on `K ⊗ᴸ -` from a morphism of quasi-coherent modules on `B`. -/
def extSourceMap (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) {F F' : Modules B} (φ : F ⟶ F') :
    extSource f H E G F ⟶ extSource f H E G F' :=
  (DerivedTensor.Bifunctor.Right.isoApp
        ((DerivedCategory.singleFunctor (Modules B) 0).obj F)
        (pushforwardInternalHom f H E G)).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor (pushforwardInternalHom f H E G)).map
      ((DerivedCategory.singleFunctor (Modules B) 0).map φ) ≫
      (DerivedTensor.Bifunctor.Right.isoApp
          ((DerivedCategory.singleFunctor (Modules B) 0).obj F')
          (pushforwardInternalHom f H E G)).inv

/-- Induced map on `ihom(E, Q(G ⊗ f^* -))` from a morphism of modules on `B`. -/
def extTargetMap (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) {F F' : Modules B} (φ : F ⟶ F') :
    extTarget f H E G F ⟶ extTarget f H E G F' :=
  (ihomOf H E).map
    (DerivedCategory.Q.map
      (HomologicalComplex.tensorHom (𝟙 G)
        ((HomologicalComplex.single (Modules X) (up ℤ) 0).map
          ((Modules.pullback f).map φ))))

/-- The Ext comparison is natural in the quasi-coherent module `F`. -/
theorem extComparison_naturality (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i))))
    {F F' : Modules B} (φ : F ⟶ F')
    (hF : quasiCoherentModuleProperty B F) (hF' : quasiCoherentModuleProperty B F') (i : ℤ) :
    extComparison f H E G F i ≫ cohomologyAb_map (extTargetMap f H E G φ) i =
      cohomologyAb_map (extSourceMap f H E G φ) i ≫ extComparison f H E G F' i :=
  sorry

/-- Connecting map on `H^i(B, K ⊗ᴸ -)` attached to a short exact sequence of modules on `B`. -/
def extSourceδ (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (s : ShortComplex (Modules B))
    (hs : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact) (i : ℤ) :
    cohomologyAb B (extSource f H E G s.X₃) i ⟶
      cohomologyAb B (extSource f H E G s.X₁) (i + 1) :=
  cohomologyAb_map
      (DerivedTensor.Bifunctor.Right.comm (pushforwardInternalHom f H E G)
        ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₃)).hom i ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
      ((moduleDerivedGlobalSectionsAb B).mapTriangle.obj
        ((DerivedTensor.Right.functor (pushforwardInternalHom f H E G)).mapTriangle.obj
          (DerivedCategory.triangleOfSES hs)))
      i (i + 1) rfl ≫
      cohomologyAb_map
        (DerivedTensor.Bifunctor.Right.comm (pushforwardInternalHom f H E G)
          ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₁)).inv (i + 1)

/-- Shift compatibility of `ihomOf H E` as the right adjoint of `tensorLeft E`. -/
noncomputable instance ihomOf_commShift (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) [(tensorLeft E).CommShift ℤ] :
    (ihomOf H E).CommShift ℤ :=
  (adjunctionOf H E).rightAdjointCommShift ℤ

/-- Connecting map on `Ext^i_{𝒪_X}(E, G ⊗ f^* -)` attached to a short exact sequence of
modules on `B`. -/
def extTargetδ (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (s : ShortComplex (Modules B))
    (hs : (complexTensorPullbackShortComplex f G s).ShortExact) (i : ℤ)
    [(tensorLeft E).CommShift ℤ] :
    cohomologyAb X (extTarget f H E G s.X₃) i ⟶
      cohomologyAb X (extTarget f H E G s.X₁) (i + 1) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
    ((moduleDerivedGlobalSectionsAb X).mapTriangle.obj
      ((ihomOf H E).mapTriangle.obj (DerivedCategory.triangleOfSES hs)))
    i (i + 1) rfl

/-- The Ext comparison commutes with connecting maps of a short exact sequence of
quasi-coherent modules on `B`. -/
theorem extComparison_boundary (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (hE : IsPerfect E)
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
    (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
    [(tensorLeft E).CommShift ℤ] :
    extComparison f H E G s.X₃ i ≫
        extTargetδ f H E G s (complexTensorPullback_shortExact f G hG_flat s hs) i =
      extSourceδ f H E G s hs0 i ≫ extComparison f H E G s.X₁ (i + 1) :=
  sorry



end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
