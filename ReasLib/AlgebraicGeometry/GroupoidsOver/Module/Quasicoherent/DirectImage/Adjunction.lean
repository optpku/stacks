/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Adjunction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback.EtaleRestriction
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Pullback/direct-image adjunction for quasi-coherent modules -/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Adjunction
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
-- The canonical equivalence retains its two private transposition functions and their laws.
set_option backward.privateInPublic true
universe u
namespace AlgebraicGeometry.GroupoidsOver.QCoh
variable {S : Scheme.{u}}

private def pullbackDirectImageTranspose {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] (F : QCoh Y) (G : QCoh X)
    (η : (pullback f).obj F ⟶ G) : F ⟶ (directImage f).obj G := by
  let D := (LQCohFbc.directImage f).obj ((toLQCohFbc X).obj G)
  let C := modulePullbackRestrictionIso f
  let E := etaleModuleHomEquiv f ((restriction Y).obj F.obj) ((restriction X).obj G.obj)
  let A := (toLQCohFbcAdjunction Y).homEquiv F D
  exact A (ObjectProperty.homMk (E (C.inv.app F.obj ≫ (restriction X).map η.hom)))

private def pullbackDirectImageUntranspose {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] (F : QCoh Y) (G : QCoh X)
    (θ : F ⟶ (directImage f).obj G) : (pullback f).obj F ⟶ G := by
  let D := (LQCohFbc.directImage f).obj ((toLQCohFbc X).obj G)
  let C := modulePullbackRestrictionIso f
  let E := etaleModuleHomEquiv f ((restriction Y).obj F.obj) ((restriction X).obj G.obj)
  let t := ((toLQCohFbcAdjunction Y).homEquiv F D).symm θ
  let s := C.hom.app F.obj ≫ E.symm t.hom
  exact (toLQCohFbc X).preimage (ObjectProperty.homMk s)

private theorem pullbackDirectImageHomEquiv_laws {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] (F : QCoh Y) (G : QCoh X) :
    (Function.LeftInverse (pullbackDirectImageUntranspose f F G)
      (pullbackDirectImageTranspose f F G)) ∧
    (Function.RightInverse (pullbackDirectImageUntranspose f F G)
      (pullbackDirectImageTranspose f F G)) ∧
    (∀ {F' : QCoh Y} (α : F' ⟶ F)
        (η : F ⟶ (directImage f).obj G),
      pullbackDirectImageUntranspose f F' G (α ≫ η) =
        (pullback f).map α ≫ pullbackDirectImageUntranspose f F G η) ∧
    (∀ {G' : QCoh X} (η : (pullback f).obj F ⟶ G) (β : G ⟶ G'),
      pullbackDirectImageTranspose f F G' (η ≫ β) =
        pullbackDirectImageTranspose f F G η ≫ (directImage f).map β) := sorry

/-- Pullback and quasi-coherent direct image have canonically equivalent Hom sets,
via étale restriction, étale transposition, and quasi-coherent coreflection. -/
def pullbackDirectImageHomEquiv {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] (F : QCoh Y) (G : QCoh X) :
    ((pullback f).obj F ⟶ G) ≃ (F ⟶ (directImage f).obj G) where
  toFun := pullbackDirectImageTranspose f F G
  invFun := pullbackDirectImageUntranspose f F G
  left_inv := (pullbackDirectImageHomEquiv_laws f F G).1
  right_inv := (pullbackDirectImageHomEquiv_laws f F G).2.1

/-- Quasi-coherent pullback is left adjoint to quasi-coherent direct image
along a quasi-compact quasi-separated morphism with small étale sections. -/
def pullbackDirectImageAdjunction {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] :
    pullback f ⊣ directImage f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pullbackDirectImageHomEquiv f
      homEquiv_naturality_left_symm := by
        intro F F' G α η
        exact (pullbackDirectImageHomEquiv_laws f F' G).2.2.1 α η
      homEquiv_naturality_right := by
        intro F G G' η β
        exact (pullbackDirectImageHomEquiv_laws f F G).2.2.2 η β }

/-- The Hom equivalence of the pullback/direct-image adjunction is canonical transposition. -/
theorem pullbackDirectImageAdjunction_homEquiv {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] (F : QCoh Y) (G : QCoh X) :
    (pullbackDirectImageAdjunction f).homEquiv F G =
      pullbackDirectImageHomEquiv f F G := by
  let c : Adjunction.CoreHomEquiv (pullback f) (directImage f) :=
    { homEquiv := pullbackDirectImageHomEquiv f
      homEquiv_naturality_left_symm := by
        intro F F' G α η
        exact (pullbackDirectImageHomEquiv_laws f F' G).2.2.1 α η
      homEquiv_naturality_right := by
        intro F G G' η β
        exact (pullbackDirectImageHomEquiv_laws f F G).2.2.2 η β }
  change (Adjunction.mkOfHomEquiv c).homEquiv F G = _
  rw [Adjunction.mkOfHomEquiv_homEquiv]

end AlgebraicGeometry.GroupoidsOver.QCoh
