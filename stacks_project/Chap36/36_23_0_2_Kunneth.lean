/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.GlobalSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u

/- The canonical global Künneth morphism provided by the shared mathematical owner. -/
#check (AlgebraicGeometry.Scheme.Modules.Kunneth.globalMap :
  ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom a.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom b.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.fst a b).toShHom a.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.snd a b).toShHom b.toShHom)]
    [(RingedSpace.modulePullbackDerived
      (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
    [MonoidalCategory
      (RingedSpace.ModuleDerived.Tensor.globalSectionsDerived S.toRingedSpace)]
    [(RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).LaxMonoidal]
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules),
    (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward a.toShHom).obj K) ⊗
        (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward b.toShHom).obj M) ⟶
      (RingedSpace.Module.Derived.GlobalSections.functor S.toRingedSpace).obj
        ((RingedSpace.moduleDerivedPushforward
          (Limits.pullback.fst a b ≫ a).toShHom).obj
            (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.externalTensorProduct a b K M)))
