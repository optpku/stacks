/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.Module.Derived
open RingedSpace.ModuleDerived
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.Kunneth

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

variable [KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [KFlat.TensorDescends S.toRingedSpace]
variable [KFlat.IsLocalization S.toRingedSpace]
variable [KFlat.HomotopyTensorDescends (Limits.pullback a b).toRingedSpace]
variable [KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
variable [KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]

variable [HasPair (RingedSpace.opensRingedSiteHom a.toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom b.toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst a b ≫ a).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.snd a b ≫ b).toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom
  ((Limits.pullback.fst a b).toShHom ≫ a.toShHom))]
variable [HasPair (RingedSpace.opensRingedSiteHom
  ((Limits.pullback.snd a b).toShHom ≫ b.toShHom))]

variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.fst a b).toShHom a.toShHom)]
variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (Limits.pullback.snd a b).toShHom b.toShHom)]
variable [(RingedSpace.modulePullbackDerived
  (Limits.pullback.fst a b ≫ a).toShHom).OplaxMonoidal]

/-- For quasi-compact and quasi-separated Tor-independent morphisms to a common base, the
canonical derived Künneth morphism is an isomorphism on objects with quasi-coherent cohomology. -/
theorem mapIsIso [QuasiCompact a] [QuasiSeparated a]
    [QuasiCompact b] [QuasiSeparated b]
    (hTor : Scheme.TorIndependentOver (Over.mk a) (Over.mk b))
    (K : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (M : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)) :
    IsIso (map a b K.obj M.obj) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.Kunneth

end
