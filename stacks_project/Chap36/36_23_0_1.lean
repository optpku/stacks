/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace.Hom
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

universe u

/- 36.23.0.1: The canonical morphism
`R(a)_* K ⊗ R(b)_* M ⟶ R(f)_* (L(p)^* K ⊗ L(q)^* M)` for `f = p ≫ a = q ≫ b`. -/
@[stacks 0FLP] #check (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.map :
  ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback a b).toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom a.toLRSHom.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom b.toLRSHom.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toLRSHom.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toLRSHom.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toLRSHom.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom))]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.snd a b).toLRSHom.toShHom ≫ b.toLRSHom.toShHom))]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.fst a b).toLRSHom.toShHom a.toLRSHom.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.snd a b).toLRSHom.toShHom b.toLRSHom.toShHom)]
    [(RingedSpace.modulePullbackDerived
      (Limits.pullback.fst a b ≫ a).toLRSHom.toShHom).OplaxMonoidal]
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (M : RingedSpace.ModuleDerived Y.toRingedSpace),
    (R(a.toLRSHom.toShHom)_*).obj K ⊗ (R(b.toLRSHom.toShHom)_*).obj M ⟶
      (R((Limits.pullback.fst a b ≫ a).toLRSHom.toShHom)_*).obj
        (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.externalTensorProduct a b K M))
