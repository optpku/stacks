/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap75.Lemma_75_23_2_Comparison

/-!
# Truncated Ext approximation and pseudo-coherent Ext representation

For a locally finite-type quasi-separated morphism of algebraic spaces and a
bounded-above coherent object `E`, Ext against `G ⊗ f^* F` is approximated in
degrees `≤ m` by tensor cohomology of a perfect complex on `B`, and is
represented in every degree by a pseudo-coherent object of `D(𝒪_B)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.Functor
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.Pretriangulated
open ComplexShape DerivedCategory.TStructure TopologicalSpace
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)] [localizationMonoidal X]

/-- Induced map on `K ⊗ᴸ -` from a morphism of modules on `B`. -/
def tensorRightSingleMap (K : ModuleDerived B) {F F' : Modules B} (φ : F ⟶ F') :
    DerivedTensor.Right.obj K ((DerivedCategory.singleFunctor (Modules B) 0).obj F) ⟶
      DerivedTensor.Right.obj K ((DerivedCategory.singleFunctor (Modules B) 0).obj F') :=
  (DerivedTensor.Bifunctor.Right.isoApp
        ((DerivedCategory.singleFunctor (Modules B) 0).obj F) K).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor K).map
      ((DerivedCategory.singleFunctor (Modules B) 0).map φ) ≫
      (DerivedTensor.Bifunctor.Right.isoApp
          ((DerivedCategory.singleFunctor (Modules B) 0).obj F') K).inv

/-- `tensorRightSingleMap` is the fixed-right derived tensor of `φ[0]`. -/
theorem tensorRightSingleMap_eq (K : ModuleDerived B) {F F' : Modules B}
    (φ : F ⟶ F') :
    tensorRightSingleMap K φ =
      (DerivedTensor.Bifunctor.Right.isoApp
            ((DerivedCategory.singleFunctor (Modules B) 0).obj F) K).hom ≫
        (DerivedTensor.Bifunctor.leftFunctor K).map
          ((DerivedCategory.singleFunctor (Modules B) 0).map φ) ≫
          (DerivedTensor.Bifunctor.Right.isoApp
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F') K).inv :=
  rfl

/-- Connecting map on `H^i(B, K ⊗ᴸ -)` attached to a short exact sequence of modules
on `B`. -/
def tensorRightSingleδ (K : ModuleDerived B) (s : ShortComplex (Modules B))
    (hs : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
    (i : ℤ) :
    cohomologyAb B
        (DerivedTensor.Right.obj K
          ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₃)) i ⟶
      cohomologyAb B
        (DerivedTensor.Right.obj K
          ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₁)) (i + 1) :=
  cohomologyAb_map
      (DerivedTensor.Bifunctor.Right.comm K
        ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₃)).hom i ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
      ((moduleDerivedGlobalSectionsAb B).mapTriangle.obj
        ((DerivedTensor.Right.functor K).mapTriangle.obj
          (DerivedCategory.triangleOfSES hs)))
      i (i + 1) rfl ≫
      cohomologyAb_map
        (DerivedTensor.Bifunctor.Right.comm K
          ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₁)).inv (i + 1)

/-- `tensorRightSingleδ` is homology of the derived-tensor triangle of `s[0]`. -/
theorem tensorRightSingleδ_eq (K : ModuleDerived B) (s : ShortComplex (Modules B))
    (hs : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
    (i : ℤ) :
    tensorRightSingleδ K s hs i =
      cohomologyAb_map
          (DerivedTensor.Bifunctor.Right.comm K
            ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₃)).hom i ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
          ((moduleDerivedGlobalSectionsAb B).mapTriangle.obj
            ((DerivedTensor.Right.functor K).mapTriangle.obj
              (DerivedCategory.triangleOfSES hs)))
          i (i + 1) rfl ≫
          cohomologyAb_map
            (DerivedTensor.Bifunctor.Right.comm K
              ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₁)).inv
            (i + 1) :=
  rfl

/-- Induced map on `ihom(L, F[0])` from a morphism of modules on `B`. -/
def representedExtMap [MonoidalCategory (ModuleDerived B)]
    (H_B : MonoidalClosed (ModuleDerived B)) (L : ModuleDerived B)
    {F F' : Modules B} (φ : F ⟶ F') :
    (ihomOf H_B L).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F) ⟶
      (ihomOf H_B L).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F') :=
  (ihomOf H_B L).map ((DerivedCategory.singleFunctor (Modules B) 0).map φ)

/-- `representedExtMap` is `ihom(L, -)` applied to `φ[0]`. -/
theorem representedExtMap_eq [MonoidalCategory (ModuleDerived B)]
    (H_B : MonoidalClosed (ModuleDerived B)) (L : ModuleDerived B)
    {F F' : Modules B} (φ : F ⟶ F') :
    representedExtMap H_B L φ =
      (ihomOf H_B L).map ((DerivedCategory.singleFunctor (Modules B) 0).map φ) :=
  rfl

/-- Shift compatibility of `ihomOf H L` on `D(𝒪_B)` as the right adjoint of
`tensorLeft L`. -/
noncomputable instance ihomOf_commShift_base
    [MonoidalCategory (ModuleDerived B)]
    (H_B : MonoidalClosed (ModuleDerived B)) (L : ModuleDerived B)
    [(tensorLeft L).CommShift ℤ] :
    (ihomOf H_B L).CommShift ℤ :=
  (adjunctionOf H_B L).rightAdjointCommShift ℤ

/-- Connecting map on `Ext^i_{𝒪_B}(L, -)` attached to a short exact sequence of
modules on `B`. -/
def representedExtδ [MonoidalCategory (ModuleDerived B)]
    (H_B : MonoidalClosed (ModuleDerived B)) (L : ModuleDerived B)
    (s : ShortComplex (Modules B))
    (hs : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
    (i : ℤ) [(tensorLeft L).CommShift ℤ] :
    cohomologyAb B
        ((ihomOf H_B L).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₃))
        i ⟶
      cohomologyAb B
        ((ihomOf H_B L).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj s.X₁))
        (i + 1) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
    ((moduleDerivedGlobalSectionsAb B).mapTriangle.obj
      ((ihomOf H_B L).mapTriangle.obj (DerivedCategory.triangleOfSES hs)))
    i (i + 1) rfl

/-- `representedExtδ` is homology of the internal-Hom triangle of `s[0]`. -/
theorem representedExtδ_eq [MonoidalCategory (ModuleDerived B)]
    (H_B : MonoidalClosed (ModuleDerived B)) (L : ModuleDerived B)
    (s : ShortComplex (Modules B))
    (hs : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
    (i : ℤ) [(tensorLeft L).CommShift ℤ] :
    representedExtδ H_B L s hs i =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
        ((moduleDerivedGlobalSectionsAb B).mapTriangle.obj
          ((ihomOf H_B L).mapTriangle.obj (DerivedCategory.triangleOfSES hs)))
        i (i + 1) rfl :=
  rfl

variable (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]

/-- Certificate that `K` is perfect and that the family `α` approximates
`Ext^i_X(E, G ⊗ f^* -)` by `H^i(B, K ⊗ᴸ -)` in degrees `≤ m`, naturally in
quasi-coherent coefficients and compatibly with connecting maps. -/
structure IsPerfectExtApproximation (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (m : ℤ)
    (K : ModuleDerived B)
    (α :
      ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
        cohomologyAb X (extTarget f H E G F) i ⟶
          cohomologyAb B
            (DerivedTensor.Right.obj K
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i) : Prop where
  /-- The approximating object `K` is perfect. -/
  isPerfect : IsPerfect K
  /-- `α` is an isomorphism in every degree `i ≤ m`. -/
  isIso_le :
    ∀ (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
      i ≤ m → IsIso (α F hF i)
  /-- `α` is natural in the quasi-coherent coefficient. -/
  naturality :
    ∀ {F F' : Modules B} (φ : F ⟶ F') (hF : quasiCoherentModuleProperty B F)
      (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
      α F hF i ≫ cohomologyAb_map (tensorRightSingleMap K φ) i =
        cohomologyAb_map (extTargetMap f H E G φ) i ≫ α F' hF' i
  /-- `α` intertwines connecting maps of a short exact sequence of quasi-coherent
  modules on `B`. -/
  boundary :
    ∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
      (hs0 : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
      (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
      (hF₁ : quasiCoherentModuleProperty B s.X₁)
      (hF₂ : quasiCoherentModuleProperty B s.X₂)
      (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
      [(tensorLeft E).CommShift ℤ],
      α s.X₃ hF₃ i ≫ tensorRightSingleδ K s hs0 i =
        extTargetδ f H E G s
            (complexTensorPullback_shortExact f G hG_flat s hs) i ≫
          α s.X₁ hF₁ (i + 1)

/-- Package the perfect truncated Ext-approximation conditions. -/
def IsPerfectExtApproximation.of (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (m : ℤ)
    (K : ModuleDerived B)
    (α :
      ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
        cohomologyAb X (extTarget f H E G F) i ⟶
          cohomologyAb B
            (DerivedTensor.Right.obj K
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i)
    (hPerfect : IsPerfect K)
    (hIso :
      ∀ (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
        i ≤ m → IsIso (α F hF i))
    (hNat :
      ∀ {F F' : Modules B} (φ : F ⟶ F') (hF : quasiCoherentModuleProperty B F)
        (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
        α F hF i ≫ cohomologyAb_map (tensorRightSingleMap K φ) i =
          cohomologyAb_map (extTargetMap f H E G φ) i ≫ α F' hF' i)
    (hBoundary :
      ∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
        (hs0 : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
        (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
        (hF₁ : quasiCoherentModuleProperty B s.X₁)
        (hF₂ : quasiCoherentModuleProperty B s.X₂)
        (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
        [(tensorLeft E).CommShift ℤ],
        α s.X₃ hF₃ i ≫ tensorRightSingleδ K s hs0 i =
          extTargetδ f H E G s
              (complexTensorPullback_shortExact f G hG_flat s hs) i ≫
            α s.X₁ hF₁ (i + 1)) :
    IsPerfectExtApproximation f H E G m K α where
  isPerfect := hPerfect
  isIso_le := hIso
  naturality := hNat
  boundary := hBoundary

/-- The truncated Ext-approximation certificate unfolds to perfectness, isomorphisms
in degrees `≤ m`, naturality, and boundary compatibility. -/
theorem IsPerfectExtApproximation.iff (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (m : ℤ)
    (K : ModuleDerived B)
    (α :
      ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
        cohomologyAb X (extTarget f H E G F) i ⟶
          cohomologyAb B
            (DerivedTensor.Right.obj K
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i) :
    IsPerfectExtApproximation f H E G m K α ↔
      IsPerfect K ∧
        (∀ (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
            i ≤ m → IsIso (α F hF i)) ∧
          (∀ {F F' : Modules B} (φ : F ⟶ F')
              (hF : quasiCoherentModuleProperty B F)
              (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
              α F hF i ≫ cohomologyAb_map (tensorRightSingleMap K φ) i =
                cohomologyAb_map (extTargetMap f H E G φ) i ≫ α F' hF' i) ∧
            ∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
              (hs0 :
                (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
              (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
              (hF₁ : quasiCoherentModuleProperty B s.X₁)
              (hF₂ : quasiCoherentModuleProperty B s.X₂)
              (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
              [(tensorLeft E).CommShift ℤ],
              α s.X₃ hF₃ i ≫ tensorRightSingleδ K s hs0 i =
                extTargetδ f H E G s
                    (complexTensorPullback_shortExact f G hG_flat s hs) i ≫
                  α s.X₁ hF₁ (i + 1) :=
  sorry

/-- Through every degree `m`, Ext against a bounded-above object with coherent
cohomology is naturally approximated by tensoring with a perfect object on `B`,
compatibly with connecting maps. -/
theorem existsPerfectExtApproximation (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X)
    (hE_minus : (t.minus : ObjectProperty (ModuleDerived X)) E)
    (hE_coherent :
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X)) E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support :
      ∀ i : ℤ,
        ClosedSubset.IsProperOver f
          (Closeds.closure (Modules.moduleSupport (G.X i))))
    (m : ℤ) :
    ∃ (K : ModuleDerived B)
      (α :
        ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
          cohomologyAb X (extTarget f H E G F) i ⟶
            cohomologyAb B
              (DerivedTensor.Right.obj K
                ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i),
      IsPerfectExtApproximation f H E G m K α :=
  sorry

/-- Certificate that `L` is pseudo-coherent and that the family `α` identifies
`Ext^i_B(L, -)` with `Ext^i_X(E, G ⊗ f^* -)` for quasi-coherent coefficients,
compatibly with connecting maps. -/
structure IsPseudoCoherentExtRepresentation
    [MonoidalCategory (ModuleDerived B)] (H : MonoidalClosed (ModuleDerived X))
    (H_B : MonoidalClosed (ModuleDerived B)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (L : ModuleDerived B)
    (α :
      ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
        cohomologyAb B
            ((ihomOf H_B L).obj
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ⟶
          cohomologyAb X (extTarget f H E G F) i) : Prop where
  /-- The representing object `L` is pseudo-coherent. -/
  isPseudoCoherent : IsPseudoCoherent B L
  /-- `α` is an isomorphism in every degree. -/
  isIso :
    ∀ (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
      IsIso (α F hF i)
  /-- `α` is natural in the quasi-coherent coefficient. -/
  naturality :
    ∀ {F F' : Modules B} (φ : F ⟶ F') (hF : quasiCoherentModuleProperty B F)
      (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
      α F hF i ≫ cohomologyAb_map (extTargetMap f H E G φ) i =
        cohomologyAb_map (representedExtMap H_B L φ) i ≫ α F' hF' i
  /-- `α` intertwines connecting maps of a short exact sequence of quasi-coherent
  modules on `B`. -/
  boundary :
    ∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
      (hs0 : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
      (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
      (hF₁ : quasiCoherentModuleProperty B s.X₁)
      (hF₂ : quasiCoherentModuleProperty B s.X₂)
      (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
      [(tensorLeft E).CommShift ℤ] [(tensorLeft L).CommShift ℤ],
      α s.X₃ hF₃ i ≫
          extTargetδ f H E G s
            (complexTensorPullback_shortExact f G hG_flat s hs) i =
        representedExtδ H_B L s hs0 i ≫ α s.X₁ hF₁ (i + 1)

/-- Package the pseudo-coherent Ext-representation conditions. -/
def IsPseudoCoherentExtRepresentation.of
    [MonoidalCategory (ModuleDerived B)] (H : MonoidalClosed (ModuleDerived X))
    (H_B : MonoidalClosed (ModuleDerived B)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (L : ModuleDerived B)
    (α :
      ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
        cohomologyAb B
            ((ihomOf H_B L).obj
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ⟶
          cohomologyAb X (extTarget f H E G F) i)
    (hPC : IsPseudoCoherent B L)
    (hIso :
      ∀ (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
        IsIso (α F hF i))
    (hNat :
      ∀ {F F' : Modules B} (φ : F ⟶ F') (hF : quasiCoherentModuleProperty B F)
        (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
        α F hF i ≫ cohomologyAb_map (extTargetMap f H E G φ) i =
          cohomologyAb_map (representedExtMap H_B L φ) i ≫ α F' hF' i)
    (hBoundary :
      ∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
        (hs0 : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
        (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
        (hF₁ : quasiCoherentModuleProperty B s.X₁)
        (hF₂ : quasiCoherentModuleProperty B s.X₂)
        (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
        [(tensorLeft E).CommShift ℤ] [(tensorLeft L).CommShift ℤ],
        α s.X₃ hF₃ i ≫
            extTargetδ f H E G s
              (complexTensorPullback_shortExact f G hG_flat s hs) i =
          representedExtδ H_B L s hs0 i ≫ α s.X₁ hF₁ (i + 1)) :
    IsPseudoCoherentExtRepresentation f H H_B E G L α where
  isPseudoCoherent := hPC
  isIso := hIso
  naturality := hNat
  boundary := hBoundary

/-- The pseudo-coherent Ext-representation certificate unfolds to pseudo-coherence,
isomorphisms in every degree, naturality, and boundary compatibility. -/
theorem IsPseudoCoherentExtRepresentation.iff
    [MonoidalCategory (ModuleDerived B)] (H : MonoidalClosed (ModuleDerived X))
    (H_B : MonoidalClosed (ModuleDerived B)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (L : ModuleDerived B)
    (α :
      ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
        cohomologyAb B
            ((ihomOf H_B L).obj
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ⟶
          cohomologyAb X (extTarget f H E G F) i) :
    IsPseudoCoherentExtRepresentation f H H_B E G L α ↔
      IsPseudoCoherent B L ∧
        (∀ (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
            IsIso (α F hF i)) ∧
          (∀ {F F' : Modules B} (φ : F ⟶ F')
              (hF : quasiCoherentModuleProperty B F)
              (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
              α F hF i ≫ cohomologyAb_map (extTargetMap f H E G φ) i =
                cohomologyAb_map (representedExtMap H_B L φ) i ≫ α F' hF' i) ∧
            ∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
              (hs0 :
                (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
              (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
              (hF₁ : quasiCoherentModuleProperty B s.X₁)
              (hF₂ : quasiCoherentModuleProperty B s.X₂)
              (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
              [(tensorLeft E).CommShift ℤ] [(tensorLeft L).CommShift ℤ],
              α s.X₃ hF₃ i ≫
                  extTargetδ f H E G s
                    (complexTensorPullback_shortExact f G hG_flat s hs) i =
                representedExtδ H_B L s hs0 i ≫ α s.X₁ hF₁ (i + 1) :=
  sorry

/-- Ext against a bounded-above object with coherent cohomology is naturally
represented in every degree by a pseudo-coherent object on `B`, compatibly with
connecting maps. -/
theorem existsPseudoCoherentExtRepresentation
    [MonoidalCategory (ModuleDerived B)] (H : MonoidalClosed (ModuleDerived X))
    (H_B : MonoidalClosed (ModuleDerived B)) (E : ModuleDerived X)
    (hE_minus : (t.minus : ObjectProperty (ModuleDerived X)) E)
    (hE_coherent :
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X)) E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support :
      ∀ i : ℤ,
        ClosedSubset.IsProperOver f
          (Closeds.closure (Modules.moduleSupport (G.X i)))) :
    ∃ (L : ModuleDerived B)
      (α :
        ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
          cohomologyAb B
              ((ihomOf H_B L).obj
                ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ⟶
            cohomologyAb X (extTarget f H E G F) i),
      IsPseudoCoherentExtRepresentation f H H_B E G L α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
