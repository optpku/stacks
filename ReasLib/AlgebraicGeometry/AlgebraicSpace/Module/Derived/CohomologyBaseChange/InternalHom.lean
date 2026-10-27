/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Criteria
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.InternalHom.Canonical

/-! # Derived Hom inheritance of geometric-point cohomology base change -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X : AlgebraicSpace S}

/-- Canonical derived sheaf Hom lifted to quasi-coherent cohomology when its cohomology
satisfies that property. -/
def internalHomObj (E : ModuleDerived X) (K : DerivedQCoh X)
    (h : derivedQuasiCoherentModuleProperty X ((ModuleDerived.InternalHom.functor E).obj K.obj)) :
    DerivedQCoh X := ⟨(ModuleDerived.InternalHom.functor E).obj K.obj, h⟩

/-- Forgetting the quasi-coherent lift recovers canonical derived sheaf Hom. -/
theorem internalHomObj_obj (E : ModuleDerived X) (K : DerivedQCoh X)
    (h : derivedQuasiCoherentModuleProperty X ((ModuleDerived.InternalHom.functor E).obj K.obj)) :
    (internalHomObj E K h).obj = (ModuleDerived.InternalHom.functor E).obj K.obj := rfl

/-- Internal Hom from the pullback of a perfect complex into a quasi-coherent complex has
quasi-coherent cohomology. -/
theorem internalHomTarget_mem_of_isPerfect (g' : X' ⟶ X) (E : ModuleDerived X)
    (K' : DerivedQCoh X') (hE : ModuleDerived.IsPerfect E) :
    derivedQuasiCoherentModuleProperty X'
      ((ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj E)).obj K'.obj) := sorry

/-- Under geometric-point cohomology base change and boundedness below of the original target,
Hom from a pulled-back pseudo-coherent complex has quasi-coherent cohomology. -/
theorem internalHomTarget_mem_of_pseudoCoherent {Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (E : ModuleDerived X) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj)
    (hα : cohomologyBaseChangeHolds sq K K' α)
    (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj) (hE : IsPseudoCoherent X E) :
    derivedQuasiCoherentModuleProperty X'
      ((ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj E)).obj K'.obj) := sorry

/-- The induced Hom base-change arrow is canonical pullback–Hom comparison followed by
covariance in the specified target morphism. -/
def internalHomBaseChangeMap (g' : X' ⟶ X) (E : ModuleDerived X)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj)
    (h_source : derivedQuasiCoherentModuleProperty X
      ((ModuleDerived.InternalHom.functor E).obj K.obj))
    (h_target : derivedQuasiCoherentModuleProperty X'
      ((ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj E)).obj K'.obj)) :
    (ModuleDerived.pullback g').obj (internalHomObj E K h_source).obj ⟶
      (internalHomObj ((ModuleDerived.pullback g').obj E) K' h_target).obj :=
  ModuleDerived.InternalHom.canonicalPullbackComparison g' E K.obj ≫
    (ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj E)).map α

/-- The underlying Hom base-change arrow is the composition of the canonical comparison and
the Hom map induced by the specified target morphism. -/
theorem internalHomBaseChangeMap_obj (g' : X' ⟶ X) (E : ModuleDerived X)
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj)
    (h_source : derivedQuasiCoherentModuleProperty X
      ((ModuleDerived.InternalHom.functor E).obj K.obj))
    (h_target : derivedQuasiCoherentModuleProperty X'
      ((ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj E)).obj K'.obj)) :
    internalHomBaseChangeMap g' E K K' α h_source h_target =
      ModuleDerived.InternalHom.canonicalPullbackComparison g' E K.obj ≫
        (ModuleDerived.InternalHom.functor ((ModuleDerived.pullback g').obj E)).map α := rfl

/-- Geometric-point cohomology base change on a cartesian square is preserved by canonical
derived sheaf Hom from a perfect complex. -/
theorem cohomologyBaseChange_internalHom_of_isPerfect {Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj) (E : ModuleDerived X)
    (hα : cohomologyBaseChangeHolds sq K K' α) (hE : ModuleDerived.IsPerfect E) :
    cohomologyBaseChangeHolds sq
      (internalHomObj E K (ModuleDerived.InternalHom.derivedQCoh_of_isPerfect E K hE))
      (internalHomObj ((ModuleDerived.pullback g').obj E) K'
        (internalHomTarget_mem_of_isPerfect g' E K' hE))
      (internalHomBaseChangeMap g' E K K' α
        (ModuleDerived.InternalHom.derivedQCoh_of_isPerfect E K hE)
        (internalHomTarget_mem_of_isPerfect g' E K' hE)) := sorry

/-- Geometric-point cohomology base change on a cartesian square is preserved by canonical
derived sheaf Hom from a pseudo-coherent complex when the original target is bounded below. -/
theorem cohomologyBaseChange_internalHom_of_isPseudoCoherent_of_boundedBelow
    {Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj) (E : ModuleDerived X)
    (hα : cohomologyBaseChangeHolds sq K K' α)
    (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj) (hE : IsPseudoCoherent X E) :
    cohomologyBaseChangeHolds sq
      (internalHomObj E K (ModuleDerived.InternalHom.derivedQCoh_of_isPseudoCoherent E K hE hK))
      (internalHomObj ((ModuleDerived.pullback g').obj E) K'
        (internalHomTarget_mem_of_pseudoCoherent g' f' f g sq E K K' α hα hK hE))
      (internalHomBaseChangeMap g' E K K' α
        (ModuleDerived.InternalHom.derivedQCoh_of_isPseudoCoherent E K hE hK)
        (internalHomTarget_mem_of_pseudoCoherent g' f' f g sq E K K' α hα hK hE)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
