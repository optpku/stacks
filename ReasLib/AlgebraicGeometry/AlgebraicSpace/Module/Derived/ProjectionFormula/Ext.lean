/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula.Cohomology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom.Functor

/-! # Projection formula for derived sheaf Hom -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory.DerivedCategory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.Pretriangulated ComplexShape TopologicalSpace
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.ExtProjectionFormula

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Derived pushforward of canonical derived sheaf Hom into a complex of modules. -/
def pushforwardHom (f : X ⟶ B) (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) : ModuleDerived B :=
  (Modules.moduleDerivedPushforward f).obj
    ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))

/-- `pushforwardHom` is derived pushforward of the derived internal Hom into `Q.obj G`. -/
theorem pushforwardHom_eq (f : X ⟶ B) (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) :
    pushforwardHom f E G =
      (Modules.moduleDerivedPushforward f).obj
        ((InternalHom.functor E).obj (DerivedCategory.Q.obj G)) :=
  rfl

/-- Source object `K ⊗ᴸ F` of the Ext comparison, with `F` placed in degree `0`. -/
def source (f : X ⟶ B) (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    ModuleDerived B :=
  DerivedTensor.Right.obj (pushforwardHom f E G)
    ((DerivedCategory.singleFunctor (Modules B) 0).obj F)

/-- `source` is fixed-right derived tensor of `pushforwardHom` with `F[0]`. -/
theorem source_eq (f : X ⟶ B) (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    source f E G F =
      DerivedTensor.Right.obj (pushforwardHom f E G)
        ((DerivedCategory.singleFunctor (Modules B) 0).obj F) :=
  rfl

/-- Target object `ihom(E, Q(G ⊗ f^* F))`, the derived internal-Hom model of
`Ext^i_{𝒪_X}(E, G ⊗ f^* F)`. -/
def target (f : X ⟶ B) (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    ModuleDerived X :=
  (InternalHom.functor E).obj (DerivedCategory.Q.obj (complexTensorPullback f G F))

/-- `target` is the derived internal Hom from `E` into `Q.obj (G ⊗ f^* F)`. -/
theorem target_eq (f : X ⟶ B) (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    target f E G F =
      (InternalHom.functor E).obj (DerivedCategory.Q.obj (complexTensorPullback f G F)) :=
  rfl

/-- Tensoring derived Hom maps to derived Hom of the tensor by transposing evaluation. -/
def tensorHomComparison (E A B : ModuleDerived X) :
    DerivedTensor.Right.obj ((InternalHom.functor E).obj A) B ⟶
      (InternalHom.functor E).obj (DerivedTensor.Bifunctor.obj A B) :=
  (InternalHom.adjunction E).homEquiv _ _ (
  (DerivedTensor.Bifunctor.Right.isoApp E
      (DerivedTensor.Right.obj ((InternalHom.functor E).obj A) B)).hom ≫
    (DerivedTensor.Bifunctor.rightFunctor E).map
      (DerivedTensor.Bifunctor.Right.isoApp B ((InternalHom.functor E).obj A)).hom ≫
    (
  let e := DerivedCategory.Q.objObjPreimageIso B
  let t := (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
      ((Iso.refl ((InternalHom.functor E).obj A)).prod e.symm) ≪≫
    (DerivedTensor.Bifunctor.Right.isoApp
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage B)) ((InternalHom.functor E).obj A)).symm
  (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso (t.prod (Iso.refl E)) ≪≫
    derivedTensorAssocComponent ((InternalHom.functor E).obj A) (DerivedCategory.Q.objPreimage B) E ≪≫
    (DerivedTensor.Bifunctor.leftFunctor ((InternalHom.functor E).obj A)).mapIso
      ((DerivedTensor.Bifunctor.rightFunctor E).mapIso e)
    ).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor ((InternalHom.functor E).obj A)).map
      (DerivedTensor.Bifunctor.comm B E).hom ≫
    (
  let e := DerivedCategory.Q.objObjPreimageIso E
  let t := (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
      ((Iso.refl ((InternalHom.functor E).obj A)).prod e.symm) ≪≫
    (DerivedTensor.Bifunctor.Right.isoApp
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E)) ((InternalHom.functor E).obj A)).symm
  (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso (t.prod (Iso.refl B)) ≪≫
    derivedTensorAssocComponent ((InternalHom.functor E).obj A) (DerivedCategory.Q.objPreimage E) B ≪≫
    (DerivedTensor.Bifunctor.leftFunctor ((InternalHom.functor E).obj A)).mapIso
      ((DerivedTensor.Bifunctor.rightFunctor B).mapIso e)
    ).inv ≫
    (DerivedTensor.Bifunctor.rightFunctor B).map
      ((DerivedTensor.Bifunctor.Right.isoApp E ((InternalHom.functor E).obj A)).inv ≫
        (InternalHom.adjunction E).counit.app A)
      )

/-- The tensor–Hom comparison is the transpose of native reassociation, symmetry,
and the counit evaluation of the tensor–Hom adjunction. -/
theorem tensorHomComparison_eq (E A B : ModuleDerived X) :
    tensorHomComparison E A B =
      (InternalHom.adjunction E).homEquiv _ _ (
  (DerivedTensor.Bifunctor.Right.isoApp E
      (DerivedTensor.Right.obj ((InternalHom.functor E).obj A) B)).hom ≫
    (DerivedTensor.Bifunctor.rightFunctor E).map
      (DerivedTensor.Bifunctor.Right.isoApp B ((InternalHom.functor E).obj A)).hom ≫
    (
  let e := DerivedCategory.Q.objObjPreimageIso B
  let t := (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
      ((Iso.refl ((InternalHom.functor E).obj A)).prod e.symm) ≪≫
    (DerivedTensor.Bifunctor.Right.isoApp
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage B)) ((InternalHom.functor E).obj A)).symm
  (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso (t.prod (Iso.refl E)) ≪≫
    derivedTensorAssocComponent ((InternalHom.functor E).obj A) (DerivedCategory.Q.objPreimage B) E ≪≫
    (DerivedTensor.Bifunctor.leftFunctor ((InternalHom.functor E).obj A)).mapIso
      ((DerivedTensor.Bifunctor.rightFunctor E).mapIso e)
    ).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor ((InternalHom.functor E).obj A)).map
      (DerivedTensor.Bifunctor.comm B E).hom ≫
    (
  let e := DerivedCategory.Q.objObjPreimageIso E
  let t := (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
      ((Iso.refl ((InternalHom.functor E).obj A)).prod e.symm) ≪≫
    (DerivedTensor.Bifunctor.Right.isoApp
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E)) ((InternalHom.functor E).obj A)).symm
  (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso (t.prod (Iso.refl B)) ≪≫
    derivedTensorAssocComponent ((InternalHom.functor E).obj A) (DerivedCategory.Q.objPreimage E) B ≪≫
    (DerivedTensor.Bifunctor.leftFunctor ((InternalHom.functor E).obj A)).mapIso
      ((DerivedTensor.Bifunctor.rightFunctor B).mapIso e)
    ).inv ≫
    (DerivedTensor.Bifunctor.rightFunctor B).map
      ((DerivedTensor.Bifunctor.Right.isoApp E ((InternalHom.functor E).obj A)).inv ≫
        (InternalHom.adjunction E).counit.app A)
      ) :=
  rfl

/-- The canonical tensor–Hom coefficient comparison, followed by the ordinary tensor counit. -/
def identification (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    DerivedTensor.Right.obj ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))
        ((modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) ⟶
      target f E G F :=
  (DerivedTensor.Bifunctor.Right.isoApp
      ((modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F))
      ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor
      ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))).map
      (pullbackDerivedSingleComparison f F) ≫
    (DerivedTensor.Bifunctor.Right.isoApp
      ((DerivedCategory.singleFunctor (Modules X) 0).obj ((Modules.pullback f).obj F))
      ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))).inv ≫
    tensorHomComparison E (DerivedCategory.Q.obj G)
      ((DerivedCategory.singleFunctor (Modules X) 0).obj ((Modules.pullback f).obj F)) ≫
    (InternalHom.functor E).map (flatTensorComparison f G F)

/-- The coefficient identification is pullback comparison, evaluation transpose, and tensor counit. -/
theorem identification_eq (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    identification f E G F =
  (DerivedTensor.Bifunctor.Right.isoApp
      ((modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F))
      ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor
      ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))).map
      (pullbackDerivedSingleComparison f F) ≫
    (DerivedTensor.Bifunctor.Right.isoApp
      ((DerivedCategory.singleFunctor (Modules X) 0).obj ((Modules.pullback f).obj F))
      ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))).inv ≫
    tensorHomComparison E (DerivedCategory.Q.obj G)
      ((DerivedCategory.singleFunctor (Modules X) 0).obj ((Modules.pullback f).obj F)) ≫
    (InternalHom.functor E).map (flatTensorComparison f G F) :=
  rfl

/-- Functorial comparison `H^i(B, K ⊗ᴸ F) ⟶ H^i(X, RHom(E, G ⊗ f^* F))`. -/
def comparison (f : X ⟶ B) (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) (i : ℤ) :
    cohomologyAb B (source f E G F) i ⟶ cohomologyAb X (target f E G F) i :=
  cohomologyAb_map
      (leftMate f ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))
        ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ≫
    moduleDerivedLerayComparison_app f
      (DerivedTensor.Right.obj ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))
        ((modulePullbackDerived f).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F)))
      i ≫
      cohomologyAb_map (identification f E G F) i

/-- `comparison` is cohomology of `leftMate`, then Leray, then the
tensor/internal-Hom identification. -/
theorem comparison_eq (f : X ⟶ B) (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) (i : ℤ) :
    comparison f E G F i =
      cohomologyAb_map
          (leftMate f ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))
            ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ≫
        moduleDerivedLerayComparison_app f
          (DerivedTensor.Right.obj ((InternalHom.functor E).obj (DerivedCategory.Q.obj G))
            ((modulePullbackDerived f).obj
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F))) i ≫
          cohomologyAb_map (identification f E G F) i :=
  rfl

/-- For a locally finite-type quasi-separated morphism to a Noetherian algebraic space,
a perfect complex, and a bounded coherent relatively flat complex with proper support,
the canonical Ext projection comparison is an isomorphism for quasi-coherent coefficients
in every integer degree. -/
theorem comparison_isIso (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
    (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i))))
    (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ) :
    IsIso (comparison f E G F i) :=
  sorry

/-- Induced map on `K ⊗ᴸ -` from a morphism of quasi-coherent modules on `B`. -/
def sourceMap (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) {F F' : Modules B} (φ : F ⟶ F') :
    source f E G F ⟶ source f E G F' :=
  (DerivedTensor.Bifunctor.Right.isoApp
        ((DerivedCategory.singleFunctor (Modules B) 0).obj F)
        (pushforwardHom f E G)).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor (pushforwardHom f E G)).map
      ((DerivedCategory.singleFunctor (Modules B) 0).map φ) ≫
      (DerivedTensor.Bifunctor.Right.isoApp
          ((DerivedCategory.singleFunctor (Modules B) 0).obj F')
          (pushforwardHom f E G)).inv

/-- Induced map on `ihom(E, Q(G ⊗ f^* -))` from a morphism of modules on `B`. -/
def targetMap (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) {F F' : Modules B} (φ : F ⟶ F') :
    target f E G F ⟶ target f E G F' :=
  (InternalHom.functor E).map
    (DerivedCategory.Q.map
      (HomologicalComplex.tensorHom (𝟙 G)
        ((HomologicalComplex.single (Modules X) (up ℤ) 0).map
          ((Modules.pullback f).map φ))))

/-- For a locally finite-type quasi-separated morphism to a Noetherian algebraic space,
a perfect complex, and a bounded coherent relatively flat complex with proper support,
the canonical Ext projection comparison is natural in quasi-coherent coefficients. -/
theorem comparison_naturality (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
    (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i))))
    {F F' : Modules B} (φ : F ⟶ F')
    (hF : quasiCoherentModuleProperty B F) (hF' : quasiCoherentModuleProperty B F') (i : ℤ) :
    comparison f E G F i ≫ cohomologyAb_map (targetMap f E G φ) i =
      cohomologyAb_map (sourceMap f E G φ) i ≫ comparison f E G F' i :=
  sorry

/-- Connecting map on `H^i(B, K ⊗ᴸ -)` attached to a short exact sequence of modules on `B`. -/
def sourceδ (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (s : ShortComplex (Modules B))
    (hs : s.ShortExact) (i : ℤ) :
    cohomologyAb B (source f E G s.X₃) i ⟶
      cohomologyAb B (source f E G s.X₁) (i + 1) :=
  cohomologyAb_map
      (DerivedTensor.Bifunctor.Right.comm (pushforwardHom f E G)
        ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₃)).hom i ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
      ((moduleDerivedGlobalSectionsAb B).mapTriangle.obj
        ((DerivedTensor.Right.functor (pushforwardHom f E G)).mapTriangle.obj
          (DerivedCategory.triangleOfSES
            (hs.map_of_exact (HomologicalComplex.single (Modules B) (up ℤ) 0)))))
      i (i + 1) rfl ≫
      cohomologyAb_map
        (DerivedTensor.Bifunctor.Right.comm (pushforwardHom f E G)
          ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₁)).inv (i + 1)

/-- Canonical derived sheaf Hom commutes with shifts by the native tensor–Hom adjunction. -/
instance homCommShift (E : ModuleDerived X) : (InternalHom.functor E).CommShift ℤ :=
  (InternalHom.adjunction E).rightAdjointCommShift ℤ

/-- Connecting map on `Ext^i_{𝒪_X}(E, G ⊗ f^* -)` attached to a short exact sequence of
modules on `B`. -/
def targetδ (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (s : ShortComplex (Modules B))
    (hs : (complexTensorPullbackShortComplex f G s).ShortExact) (i : ℤ) :
    cohomologyAb X (target f E G s.X₃) i ⟶
      cohomologyAb X (target f E G s.X₁) (i + 1) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
    ((moduleDerivedGlobalSectionsAb X).mapTriangle.obj
      ((InternalHom.functor E).mapTriangle.obj (DerivedCategory.triangleOfSES hs)))
    i (i + 1) rfl

/-- For a locally finite-type quasi-separated morphism to a Noetherian algebraic space,
a perfect complex, and a bounded coherent relatively flat complex with proper support,
the canonical Ext projection comparison commutes with the connecting maps of short exact
sequences of quasi-coherent coefficients. -/
theorem comparison_boundary
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
    comparison f E G s.X₃ i ≫
        targetδ f E G s (complexTensorPullback_shortExact f G hG_flat s hs) i =
      sourceδ f E G s hs i ≫ comparison f E G s.X₁ (i + 1) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.ExtProjectionFormula
