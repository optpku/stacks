/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
public import stacks_project.Chap75.Lemma_75_13_10_InternalHom
public import stacks_project.Chap75.Lemma_75_21_1_Criteria
public import stacks_project.Chap75.Lemma_75_21_3_Pullback

/-!
# Internal-Hom base-change comparison on algebraic spaces

A map `L(g')^* K ⟶ K'` in `D_QCoh` induces
`L(g')^* RHom(E, K) ⟶ RHom(L(g')^* E, K')` as the pullback/internal-Hom comparison
followed by covariance in `α`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- A selected derived `RHom` object equipped with a proof that its cohomology is quasi-coherent. -/
noncomputable def internalHomObj {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)]
    (RHom : ModuleDerived X ⥤ ModuleDerived X)
    (K : DerivedQCoh X)
    (h : derivedQuasiCoherentModuleProperty X (RHom.obj K.obj)) :
    DerivedQCoh X where
  obj := RHom.obj K.obj
  property := h

/-- The underlying derived module of `internalHomObj` is the selected derived `RHom`. -/
theorem internalHomObj_obj {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)]
    (RHom : ModuleDerived X ⥤ ModuleDerived X)
    (K : DerivedQCoh X)
    (h : derivedQuasiCoherentModuleProperty X (RHom.obj K.obj)) :
    (internalHomObj RHom K h).obj = RHom.obj K.obj :=
  sorry

/-- Derived pullback preserves perfect objects of `D(𝒪_X)`. -/
theorem isPerfect_pullback {X' X : AlgebraicSpace S} (g' : X' ⟶ X) {E : ModuleDerived X}
    (hE : ModuleDerived.IsPerfect E) :
    ModuleDerived.IsPerfect ((ModuleDerived.pullback g').obj E) :=
  sorry

/-- Derived pullback preserves pseudo-coherent objects of `D(𝒪_X)`. -/
theorem isPseudoCoherent_pullback {X' X : AlgebraicSpace S} (g' : X' ⟶ X)
    {E : ModuleDerived X} (hE : IsPseudoCoherent X E) :
    IsPseudoCoherent X' ((ModuleDerived.pullback g').obj E) :=
  sorry

/-- Internal Hom from the pullback of a perfect complex into an object of `D_QCoh`
again has quasi-coherent cohomology. -/
theorem internalHomTarget_mem_of_isPerfect {X' X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X')] (g' : X' ⟶ X)
    (H_X' : MonoidalClosed (ModuleDerived X')) (E : ModuleDerived X)
    (K' : DerivedQCoh X') (hE : ModuleDerived.IsPerfect E) :
    derivedQuasiCoherentModuleProperty X'
      ((ihomOf H_X' ((ModuleDerived.pullback g').obj E)).obj K'.obj) :=
  sorry

/-- Under cohomology base change for `K ⟶ K'` and boundedness below of `K`, internal Hom
from the pullback of a pseudo-coherent complex into `K'` has quasi-coherent cohomology. -/
theorem internalHomTarget_mem_of_pseudoCoherent {X' X Y' Y : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X')] (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback g' f' f g)
    (H_X' : MonoidalClosed (ModuleDerived X')) (E : ModuleDerived X)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (hα : cohomologyBaseChangeHolds sq K K' α)
    (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj)
    (hE : IsPseudoCoherent X E) :
    derivedQuasiCoherentModuleProperty X'
      ((ihomOf H_X' ((ModuleDerived.pullback g').obj E)).obj K'.obj) :=
  sorry

variable {X' X : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]

/-- The comparison `L(g')^* RHom(E, K) ⟶ RHom(L(g')^* E, K')` associated to
`α : L(g')^* K ⟶ K'`. -/
noncomputable def internalHomBaseChangeMap (g' : X' ⟶ X)
    [(ModuleDerived.pullback g').Monoidal]
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (E : ModuleDerived X) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶
      (inclusion X').obj K')
    (h_source : derivedQuasiCoherentModuleProperty X ((ihomOf H_X E).obj K.obj))
    (h_target : derivedQuasiCoherentModuleProperty X'
      ((ihomOf H_X' ((ModuleDerived.pullback g').obj E)).obj K'.obj)) :
    (ModuleDerived.pullback g').obj
      ((inclusion X).obj (internalHomObj (ihomOf H_X E) K h_source)) ⟶
      (inclusion X').obj
        (internalHomObj (ihomOf H_X' ((ModuleDerived.pullback g').obj E)) K' h_target) :=
  Functor.PullbackInternalHom.comparisonOf H_X H_X' (ModuleDerived.pullback g')
      (fun A B ↦ (Functor.Monoidal.μIso (ModuleDerived.pullback g') A B).symm)
      E K.obj ≫
    (ihomOf H_X' ((ModuleDerived.pullback g').obj E)).map α

/-- After forgetting `D_QCoh`, `internalHomBaseChangeMap` is the pullback/internal-Hom
comparison followed by the morphism induced by `α`. -/
theorem internalHomBaseChangeMap_obj (g' : X' ⟶ X)
    [(ModuleDerived.pullback g').Monoidal]
    (H_X : MonoidalClosed (ModuleDerived X))
    (H_X' : MonoidalClosed (ModuleDerived X'))
    (E : ModuleDerived X) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶
      (inclusion X').obj K')
    (h_source : derivedQuasiCoherentModuleProperty X ((ihomOf H_X E).obj K.obj))
    (h_target : derivedQuasiCoherentModuleProperty X'
      ((ihomOf H_X' ((ModuleDerived.pullback g').obj E)).obj K'.obj)) :
    internalHomBaseChangeMap g' H_X H_X' E K K' α h_source h_target =
      Functor.PullbackInternalHom.comparisonOf H_X H_X' (ModuleDerived.pullback g')
          (fun A B ↦ (Functor.Monoidal.μIso (ModuleDerived.pullback g') A B).symm)
          E K.obj ≫
        (ihomOf H_X' ((ModuleDerived.pullback g').obj E)).map α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
