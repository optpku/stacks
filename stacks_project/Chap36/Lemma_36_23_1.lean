module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.GlobalSections.TorIndependence
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.Module.Derived
open RingedSpace.ModuleDerived
open RingedSite.Hom.DerivedAdjunction

universe u

/- Lemma 36.23.1 (1): for quasi-compact and quasi-separated morphisms from
Tor-independent schemes over a common base, the canonical derived Künneth morphism is an
isomorphism on objects of `D_QCoh`. -/
@[stacks 0FLQ] #check (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.mapIsIso :
  ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [KFlat.HomotopyTensorDescends (Limits.pullback a b).toRingedSpace]
    [KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
    [KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom a.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom b.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom
      ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
    [HasPair (RingedSpace.opensRingedSiteHom
      ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.fst a b).toShHom a.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.snd a b).toShHom b.toShHom)]
    [(RingedSpace.modulePullbackDerived
      (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : Scheme.TorIndependentOver (Over.mk a) (Over.mk b))
    (K : Scheme.DerivedQCoh X) (M : Scheme.DerivedQCoh Y),
    IsIso (AlgebraicGeometry.Scheme.ModuleDerived.Kunneth.map a b K.obj M.obj))

/- Lemma 36.23.1 (2): when the common base is affine, the canonical global Künneth
morphism for quasi-compact and quasi-separated Tor-independent schemes is an isomorphism on
objects of `D_QCoh`. -/
@[stacks 0FLQ] #check (AlgebraicGeometry.Scheme.Modules.Kunneth.globalMapIsIso :
  ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [KFlat.HomotopyTensorDescends (Limits.pullback a b).toRingedSpace]
    [KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
    [KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom a.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom b.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom
      ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
    [HasPair (RingedSpace.opensRingedSiteHom
      ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.fst a b).toShHom a.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      (Limits.pullback.snd a b).toShHom b.toShHom)]
    [(RingedSpace.modulePullbackDerived
      (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]
    [MonoidalCategory (Tensor.globalSectionsDerived S.toRingedSpace)]
    [(GlobalSections.functor S.toRingedSpace).LaxMonoidal]
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b] [IsAffine S]
    (hTor : Scheme.TorIndependentOver (Over.mk a) (Over.mk b))
    (K : Scheme.DerivedQCoh X) (M : Scheme.DerivedQCoh Y),
    IsIso (AlgebraicGeometry.Scheme.Modules.Kunneth.globalMap a b K.obj M.obj))
