/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived
open CategoryTheory.DerivedCategory
open DerivedTensor.Right.Monoidal
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

/- Lemma 36.30.1 (1): for a morphism of finite presentation, the derived pushforward of the
tensor product of a perfect object with a bounded complex of finitely presented modules that
is flat with proper support over the base is perfect. -/
@[stacks 0A1H] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_tensor_isPerfect_of_finitePresentation :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (G : CochainComplex X.Modules ℤ)
    (hG_bounded : CochainComplex.bounded X.Modules G)
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f (G.X n)],
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))))

/- Lemma 36.30.1 (2): under the same hypotheses, the tensor-pushforward comparison with the
pushforward formed from ordinary termwise pullback is an isomorphism for every cartesian base
change. -/
@[stacks 0A1H] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_tensor_baseChange_isIso_of_finitePresentation :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (G : CochainComplex X.Modules ℤ)
    (hG_bounded : CochainComplex.bounded X.Modules G)
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
      g' f' f g sq T_X T_X' ((Scheme.PerfectDerived.toDerivedQCoh X).obj ⟨E, hE⟩) G))
