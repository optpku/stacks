/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.TorIndependence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.Kunneth

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization S.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
  (pullback a b).toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends
  (pullback a b).toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization
  (pullback a b).toRingedSpace]

variable [HasPair (RingedSpace.opensRingedSiteHom a.toLRSHom.toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom b.toLRSHom.toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (pullback.fst a b).toLRSHom.toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (pullback.snd a b).toLRSHom.toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (pullback.fst a b ≫ a).toLRSHom.toShHom)]
variable [HasPair
  (RingedSpace.opensRingedSiteHom (pullback.snd a b ≫ b).toLRSHom.toShHom)]
variable [HasPair (RingedSpace.opensRingedSiteHom
  ((pullback.fst a b).toLRSHom.toShHom ≫ a.toLRSHom.toShHom))]
variable [HasPair (RingedSpace.opensRingedSiteHom
  ((pullback.snd a b).toLRSHom.toShHom ≫ b.toLRSHom.toShHom))]

variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (pullback.fst a b).toLRSHom.toShHom a.toLRSHom.toShHom)]
variable [IsIso (RingedSpace.modulePullbackDerived.compComparison
  (pullback.snd a b).toLRSHom.toShHom b.toLRSHom.toShHom)]
variable [(RingedSpace.modulePullbackDerived
  (pullback.fst a b ≫ a).toLRSHom.toShHom).OplaxMonoidal]
variable [(RingedSpace.modulePullbackDerived
  (pullback.fst a b).toLRSHom.toShHom).Monoidal]
variable [(RingedSpace.modulePullbackDerived
  (pullback.snd a b).toLRSHom.toShHom).Monoidal]

variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived (pullback a b).toRingedSpace)]

/-- For quasi-compact and quasi-separated Tor-independent morphisms to a common base, the
canonical internal-Hom Künneth morphism is an isomorphism when its source objects are perfect
and its target objects have quasicoherent cohomology. -/
theorem homMapIsIso [QuasiCompact a] [QuasiSeparated a]
    [QuasiCompact b] [QuasiSeparated b]
    (hTor : Scheme.TorIndependentOver (Over.mk a) (Over.mk b))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (K' : Scheme.ModuleDerived.Quasicoherent X)
    (M : RingedSpace.ModuleDerived Y.toRingedSpace)
    (M' : Scheme.ModuleDerived.Quasicoherent Y)
    (hK : RingedSpace.ModuleDerived.IsPerfect K)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) :
    IsIso (homMap a b K K'.obj M M'.obj) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.Kunneth

end
