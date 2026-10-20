module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.TorIndependence

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.Module.Derived
open RingedSpace.ModuleDerived
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kunneth

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
variable [MonoidalCategory (Tensor.globalSectionsDerived S.toRingedSpace)]
variable [(GlobalSections.functor S.toRingedSpace).LaxMonoidal]

/-- Over an affine base, the global-sections Künneth morphism for quasi-compact and
quasi-separated Tor-independent morphisms is an isomorphism on objects with quasi-coherent
cohomology. -/
theorem globalMapIsIso [QuasiCompact a] [QuasiSeparated a]
    [QuasiCompact b] [QuasiSeparated b] [IsAffine S]
    (hTor : Scheme.TorIndependentOver (Over.mk a) (Over.mk b))
    (K : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (M : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)) :
    IsIso (globalMap a b K.obj M.obj) := sorry

end AlgebraicGeometry.Scheme.Modules.Kunneth

end
