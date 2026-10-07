module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.InternalHom

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.Scheme.DerivedQCoh
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed
open RingedSite.Hom
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

/- Lemma 36.30.7 (1): if `f : X ⟶ S` is of finite presentation, `E` is perfect, and
`G` is a bounded complex whose terms are finitely presented, flat over `S`, and have proper
support over `S`, then `Rf_* RHom(E, Q(G))` is perfect. -/
@[stacks 0A1J] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_internalHom_isPerfect_of_finitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (hE : RingedSpace.ModuleDerived.IsPerfect E)
      (G : CochainComplex X.Modules ℤ)
      (hG_bounded : CochainComplex.bounded X.Modules G)
      [∀ n : ℤ, (G.X n).IsFinitePresentation]
      [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
      [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f (G.X n)],
      RingedSpace.ModuleDerived.IsPerfect
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          (E ⟹ DerivedCategory.Q.obj G)))

/- Lemma 36.30.7 (2): under the same hypotheses, formation of `Rf_* RHom(E, Q(G))`
commutes with every cartesian base change via the canonical comparison map. -/
@[stacks 0A1J] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_internalHom_baseChange_isIso_of_finitePresentation :
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
      (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace)),
      IsIso (internalHomPushforwardBaseChangeMap
        g' f' f g sq H_X H_X' E G))
