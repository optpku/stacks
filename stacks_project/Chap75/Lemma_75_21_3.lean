/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.InternalHom

/-! # Inheritance of geometric-point cohomology base change -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- 0DKI::statement_repair::1 (1) -/
@[stacks 0DKI] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.cohomologyBaseChange_tensor :
    ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    {Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj)
    (E : DerivedQCoh X) (hα : cohomologyBaseChangeHolds sq K K' α),
    cohomologyBaseChangeHolds sq (tensorObj E K) (tensorObj ((pullback g').obj E) K')
      (tensorBaseChangeMap g' E K K' α))

/- 0DKI::statement_repair::1 (2) -/
@[stacks 0DKI] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.cohomologyBaseChange_internalHom_of_isPerfect :
    ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    {Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj) (E : ModuleDerived X)
    (hα : cohomologyBaseChangeHolds sq K K' α) (hE : ModuleDerived.IsPerfect E),
    cohomologyBaseChangeHolds sq
      (internalHomObj E K (ModuleDerived.InternalHom.derivedQCoh_of_isPerfect E K hE))
      (internalHomObj ((ModuleDerived.pullback g').obj E) K'
        (internalHomTarget_mem_of_isPerfect g' E K' hE))
      (internalHomBaseChangeMap g' E K K' α
        (ModuleDerived.InternalHom.derivedQCoh_of_isPerfect E K hE)
        (internalHomTarget_mem_of_isPerfect g' E K' hE)))

/- 0DKI::statement_repair::1 (3) -/
@[stacks 0DKI] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.cohomologyBaseChange_internalHom_of_isPseudoCoherent_of_boundedBelow :
    ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    {Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj) (E : ModuleDerived X)
    (hα : cohomologyBaseChangeHolds sq K K' α)
    (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj) (hE : IsPseudoCoherent X E),
    cohomologyBaseChangeHolds sq
      (internalHomObj E K (ModuleDerived.InternalHom.derivedQCoh_of_isPseudoCoherent E K hE hK))
      (internalHomObj ((ModuleDerived.pullback g').obj E) K'
        (internalHomTarget_mem_of_pseudoCoherent g' f' f g sq E K K' α hα hK hE))
      (internalHomBaseChangeMap g' E K K' α
        (ModuleDerived.InternalHom.derivedQCoh_of_isPseudoCoherent E K hE hK)
        (internalHomTarget_mem_of_pseudoCoherent g' f' f g sq E K K' α hα hK hE)))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
