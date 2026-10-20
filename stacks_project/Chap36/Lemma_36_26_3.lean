/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Tensor

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived
open CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

/- Lemma 36.26.3 (1): pointwise cohomology base change is preserved after derived tensoring
by a complex with quasicoherent cohomology. -/
@[stacks 0DJA]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.cohomologyBaseChange_tensor :
  ∀ {X' X S' S : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    (g' : X' ⟶ X)
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (T_X : @Right.Monoidal.Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model
      (RingedSpace.Modules X'.toRingedSpace) _ _ _ _ _ _ _)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (K : Scheme.ModuleDerived.Quasicoherent X)
    (K' : Scheme.ModuleDerived.Quasicoherent X')
    (α : (Scheme.DerivedQCoh.pullback g').obj K ⟶ K')
    (E : Scheme.ModuleDerived.Quasicoherent X)
    [∀ (x' : X') (i : ℤ), IsIso
      ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap
        K K' α x' i)],
    ∀ (x' : X') (i : ℤ), IsIso
      ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap
        (Scheme.DerivedQCoh.tensorObj E K)
        (Scheme.DerivedQCoh.tensorObj ((Scheme.DerivedQCoh.pullback g').obj E) K')
        (Scheme.DerivedQCoh.tensorBaseChangeMap g' T_X T_X' E K K' α) x' i))

/- Lemma 36.26.3 (2): pointwise cohomology base change is preserved by derived internal Hom
from a perfect ambient derived module. -/
@[stacks 0DJA]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.cohomologyBaseChange_internalHom_of_isPerfect :
  ∀ {X' X S' S : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (sq : IsPullback g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (K : Scheme.ModuleDerived.Quasicoherent X)
    (K' : Scheme.ModuleDerived.Quasicoherent X')
    (α : (Scheme.DerivedQCoh.pullback g').obj K ⟶ K')
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    [∀ (x' : X') (i : ℤ), IsIso
      ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap
        K K' α x' i)],
    ∀ (x' : X') (i : ℤ), IsIso
      ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap
        (Scheme.DerivedQCoh.internalHomObj H_X E K
          (Scheme.ModuleDerived.InternalHom.derivedQCoh_of_perfect H_X E K hE))
        (Scheme.DerivedQCoh.internalHomObj H_X'
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj E) K'
          (Scheme.DerivedQCoh.internalHomTarget_mem_of_isPerfect g' H_X' E K' hE))
        (Scheme.DerivedQCoh.internalHomBaseChangeMap g' H_X H_X' E K K' α
          (Scheme.ModuleDerived.InternalHom.derivedQCoh_of_perfect H_X E K hE)
          (Scheme.DerivedQCoh.internalHomTarget_mem_of_isPerfect g' H_X' E K' hE)) x' i))

/- Lemma 36.26.3 (3): if `K` is bounded below, pointwise cohomology base change is
preserved by derived internal Hom from a pseudo-coherent ambient derived module. -/
@[stacks 0DJA]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.cohomologyBaseChange_internalHom_of_isPseudoCoherent_of_boundedBelow :
  ∀ {X' X S' S : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (sq : IsPullback g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (K : Scheme.ModuleDerived.Quasicoherent X)
    (K' : Scheme.ModuleDerived.Quasicoherent X')
    (α : (Scheme.DerivedQCoh.pullback g').obj K ⟶ K')
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : (t.plus : ObjectProperty
      (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E)
    [∀ (x' : X') (i : ℤ), IsIso
      ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap
        K K' α x' i)],
    ∀ (x' : X') (i : ℤ), IsIso
      ((Scheme.DerivedQCoh.CohomologyBaseChangeModel.canonical g' f' f g sq).pointMap
        (Scheme.DerivedQCoh.internalHomObj H_X E K
          (Scheme.ModuleDerived.InternalHom.derivedQCoh_of_pseudoCoherent H_X E K hE hK))
        (Scheme.DerivedQCoh.internalHomObj H_X'
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj E) K'
          (Scheme.DerivedQCoh.internalHomTarget_mem_of_pseudoCoherent
            g' f' f g sq H_X' E K K' α hK hE))
        (Scheme.DerivedQCoh.internalHomBaseChangeMap g' H_X H_X' E K K' α
          (Scheme.ModuleDerived.InternalHom.derivedQCoh_of_pseudoCoherent H_X E K hE hK)
          (Scheme.DerivedQCoh.internalHomTarget_mem_of_pseudoCoherent
            g' f' f g sq H_X' E K K' α hK hE)) x' i))

end
