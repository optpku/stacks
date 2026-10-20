/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Pushforward.Tensor
public import stacks_project.Chap36.Lemma_36_10_1_PseudoCoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived
open CategoryTheory.DerivedCategory
open DerivedTensor.Right.Monoidal
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

/- Lemma 36.30.3 (1): if `f : X ⟶ S` is of finite presentation, `E` is pseudo-coherent,
and `G` is a bounded-above complex whose terms are finitely presented, flat over `S`, and
have proper support over `S`, then the derived pushforward of `E ⊗ᴸ Q(G)` is
pseudo-coherent. -/
@[stacks 0CSC] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_tensor_isPseudoCoherent_of_finitePresentation :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E)
    (G : CochainComplex X.Modules ℤ)
    (hG_boundedAbove : CochainComplex.minus X.Modules G)
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f (G.X n)],
    RingedSpace.ModuleDerived.IsPseudoCoherent
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))))

/- Lemma 36.30.3 (2): under the same hypotheses, formation of the derived pushforward of
`E ⊗ᴸ Q(G)` commutes with every cartesian base change, meaning that the canonical
tensor-specific comparison to the pushforward formed using the ordinary termwise pullback of
`G` is an isomorphism. -/
@[stacks 0CSC] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_tensor_baseChange_isIso_of_pseudoCoherent :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E)
    (G : CochainComplex X.Modules ℤ)
    (hG_boundedAbove : CochainComplex.minus X.Modules G)
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f (G.X n)]
    {X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S)
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (sq : IsPullback g' f' f g)
    (T_X : @Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_X' : @Model
      (RingedSpace.Modules X'.toRingedSpace) _ _ _ _ _ _ _),
    IsIso (Scheme.DerivedQCoh.tensorPushforwardBaseChangeMap
      g' f' f g sq T_X T_X'
        ⟨E, AlgebraicGeometry.Scheme.ModuleDerived.PseudoCoherent.derivedQuasiCoherentModuleProperty
          hE⟩ G))
