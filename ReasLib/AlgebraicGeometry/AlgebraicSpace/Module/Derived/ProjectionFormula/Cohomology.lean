/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.ProjectionFormula
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor.Associativity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Leray

/-! # Cohomology of the projection formula with a relatively flat complex -/

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

/-- Derived pushforward of the derived tensor of a derived module and a complex. -/
def pushforwardTensor (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) : ModuleDerived B :=
  (Modules.moduleDerivedPushforward f).obj
    (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))

/-- `pushforwardTensor` is derived pushforward of the fixed-right derived tensor with
`Q.obj G`. -/
theorem pushforwardTensor_eq (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) :
    pushforwardTensor f E G =
      (Modules.moduleDerivedPushforward f).obj
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

/-- The canonical comparison from derived tensor with the pulled-back module to the
ordinary tensor complex `(Q G) ⊗ᴸ (f^* F)[0] ⟶ Q(G ⊗ f^* F)`. -/
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

/-- Canonical comparison `(E ⊗ᴸ G) ⊗ᴸ Lf^* F ⟶ E ⊗ᴸ Q(G ⊗ f^* F)`, formed
from the pullback counit, derived associativity, and the ordinary tensor comparison. -/
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

variable (f : X ⟶ B)

/-- For a locally of finite type quasi-separated morphism to a Noetherian algebraic space,
a perfect derived module, and a bounded coherent relatively flat complex with proper support,
the canonical tensor cohomology comparison is an isomorphism for every quasi-coherent module
and every integer degree. -/
theorem cohomologyComparison_isIso
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
    (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
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

/-- For a locally of finite type quasi-separated morphism to a Noetherian algebraic space,
a perfect derived module, and a bounded coherent relatively flat complex with proper support,
the tensor cohomology comparison is natural in morphisms of quasi-coherent modules. -/
theorem cohomologyComparison_naturality
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
    (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
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
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f) (s : ShortComplex (Modules B))
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

/-- For a locally of finite type quasi-separated morphism to a Noetherian algebraic space,
a perfect derived module, and a bounded coherent relatively flat complex with proper support,
the tensor cohomology comparison commutes with the connecting maps of every short exact
sequence of quasi-coherent modules. -/
theorem cohomologyComparison_boundary
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
    (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i))))
    (s : ShortComplex (Modules B)) (hs : s.ShortExact)
    (hF₁ : quasiCoherentModuleProperty B s.X₁)
    (hF₂ : quasiCoherentModuleProperty B s.X₂)
    (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ) :
    cohomologyComparison f E G s.X₃ i ≫
        cohomologyTargetδ f E G s (complexTensorPullback_shortExact f G hG_flat s hs) i =
      cohomologySourceδ f E G s
        (hs.map_of_exact (HomologicalComplex.single (Modules B) (up ℤ) 0)) i ≫
          cohomologyComparison f E G s.X₁ (i + 1) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
