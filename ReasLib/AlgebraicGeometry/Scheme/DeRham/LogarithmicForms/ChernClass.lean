/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ChernClass
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.LocallyRinged
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.LogarithmicForms

variable {X S : Scheme.{u}}

/-- The structure sheaf of a scheme is locally ringed on its small opens site. -/
instance schemeSheafIsLocallyRinged (X : Scheme.{u}) : X.sheaf.IsLocallyRinged :=
  RingedSpace.StalkLocalRing.instIsLocallyRinged X.toRingedSpace

/-- The small-universe Ext structure used for additive sheaves on the small site of a scheme. -/
noncomputable instance hasExtAddCommGrpSheaf (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  CategoryTheory.hasExt_of_enoughInjectives _

/-- Cohomology of the additive logarithmic-form subsheaf. -/
abbrev H (f : X ⟶ S) (i q : ℕ) : Type u :=
  Sheaf.H.{u} (logarithmicForms f i :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) q

/-- Logarithmic-form cohomology is sheaf cohomology of `logarithmicForms f i`. -/
theorem H_def (f : X ⟶ S) (i q : ℕ) :
    H f i q = Sheaf.H.{u} (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) q := sorry

/-- The canonical homomorphism from the Picard group to first logarithmic-form cohomology. -/
noncomputable def firstChernHom (f : X ⟶ S) : X.PicardGroup →+ H f 1 1 :=
  (Sheaf.H.map (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.dlog f) 1).comp
    (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf)

/-- The logarithmic first-Chern homomorphism is the Picard cohomology class followed by
the cohomology map induced by `dlog`. -/
theorem firstChernHom_apply (f : X ⟶ S) (x : X.PicardGroup) :
    firstChernHom f x = Sheaf.H.map
      (AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.dlog f) 1
      (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf x) := sorry

/-- The logarithmic first Chern class of an invertible module. -/
noncomputable def firstChernClass (f : X ⟶ S)
    (L : X.Modules) [Scheme.Modules.Invertible L] : H f 1 1 :=
  firstChernHom f (Scheme.Modules.picardClass L)

/-- The logarithmic first Chern class is obtained by applying `firstChernHom` to the
Picard class. -/
theorem firstChernClass_eq (f : X ⟶ S)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    firstChernClass f L = firstChernHom f (Scheme.Modules.picardClass L) := sorry

/-- The map on cohomology induced by the inclusion of logarithmic forms into all relative
differential forms. -/
noncomputable def toAmbientCohomology (f : X ⟶ S) (i q : ℕ) :
    H f i q →+ Sheaf.H.{u} (additiveTerm f i) q :=
  Sheaf.H.map (logarithmicForms f i).arrow q

/-- The logarithmic-to-ambient cohomology map is induced by the subsheaf inclusion. -/
theorem toAmbientCohomology_apply (f : X ⟶ S) (i q : ℕ) (x : H f i q) :
    toAmbientCohomology f i q x =
      Sheaf.H.map (logarithmicForms f i).arrow q x := sorry

/-- The inclusion of logarithmic one-forms is compatible with `dlog` on cohomology. -/
theorem toAmbientCohomology_dlog (f : X ⟶ S) :
    (toAmbientCohomology f 1 1).comp (Sheaf.H.map (dlog f) 1) =
      Sheaf.H.map (ambientDlog f) 1 := sorry

/-- The canonical comparison data from logarithmic first cohomology to the truncated,
de Rham, and Hodge realizations, together with the lower cohomology squares that characterize
those maps. -/
structure ChernComparison (f : X ⟶ S) where
  /-- The existing first-Chern and cup-product realization. -/
  chern : ChernClassContext f
  /-- The map induced by `toDeRham f 1` into the truncation `σ≥1 Ωᵈᴿ[f]`. -/
  toTruncated : H f 1 1 →+ hodgeSource f 1 2
  /-- The map induced by `toDeRham f 1` into the full relative de Rham complex. -/
  toDeRhamCohomology : H f 1 1 →+ cohomology f 2
  /-- The comparison from additive-sheaf cohomology of `Ω¹_[X/S]` to Hodge cohomology. -/
  ambientToHodge : Sheaf.H.{u} (additiveTerm f 1) 1 →+ hodgeCohomology f 1 1
  /-- The units-to-truncation map occurring below the logarithmic comparison. -/
  unitsToTruncated : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+
    hodgeSource f 1 2
  /-- The units-to-de Rham map occurring below the logarithmic comparison. -/
  unitsToDeRham : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+ cohomology f 2
  /-- The units-to-Hodge map occurring below the logarithmic comparison. -/
  unitsToHodge : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+
    hodgeCohomology f 1 1
  /-- The truncation comparison is induced by logarithmic `dlog`. -/
  toTruncated_dlog : toTruncated.comp (Sheaf.H.map (dlog f) 1) = unitsToTruncated
  /-- The units-to-truncation map agrees with the first-Chern realization on Picard classes. -/
  unitsToTruncated_picard : unitsToTruncated.comp
    (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
      chern.dlogCohomologyMap
  /-- The de Rham comparison is induced by logarithmic `dlog`. -/
  toDeRham_dlog : toDeRhamCohomology.comp (Sheaf.H.map (dlog f) 1) = unitsToDeRham
  /-- The units-to-de Rham map agrees with the de Rham first-Chern realization. -/
  unitsToDeRham_picard : unitsToDeRham.comp
    (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
      chern.deRhamFirstChern
  /-- The ambient one-form comparison is induced by ambient `dlog`. -/
  ambientToHodge_dlog : ambientToHodge.comp (Sheaf.H.map (ambientDlog f) 1) =
    unitsToHodge
  /-- The units-to-Hodge map agrees with the Hodge first-Chern realization. -/
  unitsToHodge_picard : unitsToHodge.comp
    (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
      chern.hodgeFirstChern

namespace ChernComparison

/-- Build the logarithmic Chern comparison from its three maps and their canonical lower
cohomology squares. -/
noncomputable def ofMaps (f : X ⟶ S) (chern : ChernClassContext f)
    (toTruncated : H f 1 1 →+ hodgeSource f 1 2)
    (toDeRhamCohomology : H f 1 1 →+ cohomology f 2)
    (ambientToHodge : Sheaf.H.{u} (additiveTerm f 1) 1 →+ hodgeCohomology f 1 1)
    (unitsToTruncated : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+
      hodgeSource f 1 2)
    (unitsToDeRham : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+ cohomology f 2)
    (unitsToHodge : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+
      hodgeCohomology f 1 1)
    (toTruncated_dlog : toTruncated.comp (Sheaf.H.map (dlog f) 1) = unitsToTruncated)
    (unitsToTruncated_picard : unitsToTruncated.comp
      (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
        chern.dlogCohomologyMap)
    (toDeRham_dlog : toDeRhamCohomology.comp (Sheaf.H.map (dlog f) 1) = unitsToDeRham)
    (unitsToDeRham_picard : unitsToDeRham.comp
      (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
        chern.deRhamFirstChern)
    (ambientToHodge_dlog : ambientToHodge.comp (Sheaf.H.map (ambientDlog f) 1) =
      unitsToHodge)
    (unitsToHodge_picard : unitsToHodge.comp
      (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
        chern.hodgeFirstChern) : ChernComparison f where
  chern := chern
  toTruncated := toTruncated
  toDeRhamCohomology := toDeRhamCohomology
  ambientToHodge := ambientToHodge
  unitsToTruncated := unitsToTruncated
  unitsToDeRham := unitsToDeRham
  unitsToHodge := unitsToHodge
  toTruncated_dlog := toTruncated_dlog
  unitsToTruncated_picard := unitsToTruncated_picard
  toDeRham_dlog := toDeRham_dlog
  unitsToDeRham_picard := unitsToDeRham_picard
  ambientToHodge_dlog := ambientToHodge_dlog
  unitsToHodge_picard := unitsToHodge_picard

/-- The Hodge comparison for logarithmic forms is inclusion into ambient one-forms followed
by the ambient Hodge comparison. -/
noncomputable def toHodge {f : X ⟶ S} (C : ChernComparison f) :
    H f 1 1 →+ hodgeCohomology f 1 1 :=
  C.ambientToHodge.comp (toAmbientCohomology f 1 1)

/-- The logarithmic-to-Hodge comparison applies by first passing to ambient one-forms. -/
theorem toHodge_apply {f : X ⟶ S} (C : ChernComparison f) (x : H f 1 1) :
    C.toHodge x = C.ambientToHodge (toAmbientCohomology f 1 1 x) := sorry

/-- The comparison built by `ofMaps` retains the supplied Chern-class realization. -/
theorem ofMaps_chern (f : X ⟶ S) (chern : ChernClassContext f)
    (toTruncated : H f 1 1 →+ hodgeSource f 1 2)
    (toDeRhamCohomology : H f 1 1 →+ cohomology f 2)
    (ambientToHodge : Sheaf.H.{u} (additiveTerm f 1) 1 →+ hodgeCohomology f 1 1)
    (unitsToTruncated : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+
      hodgeSource f 1 2)
    (unitsToDeRham : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+ cohomology f 2)
    (unitsToHodge : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+
      hodgeCohomology f 1 1)
    (toTruncated_dlog : toTruncated.comp (Sheaf.H.map (dlog f) 1) = unitsToTruncated)
    (unitsToTruncated_picard : unitsToTruncated.comp
      (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
        chern.dlogCohomologyMap)
    (toDeRham_dlog : toDeRhamCohomology.comp (Sheaf.H.map (dlog f) 1) = unitsToDeRham)
    (unitsToDeRham_picard : unitsToDeRham.comp
      (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
        chern.deRhamFirstChern)
    (ambientToHodge_dlog : ambientToHodge.comp (Sheaf.H.map (ambientDlog f) 1) =
      unitsToHodge)
    (unitsToHodge_picard : unitsToHodge.comp
      (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
        chern.hodgeFirstChern) :
    (ofMaps f chern toTruncated toDeRhamCohomology ambientToHodge unitsToTruncated
      unitsToDeRham unitsToHodge toTruncated_dlog unitsToTruncated_picard
      toDeRham_dlog unitsToDeRham_picard ambientToHodge_dlog
      unitsToHodge_picard).chern = chern := sorry

end ChernComparison

/-- The canonical truncation comparison sends the logarithmic first Chern class to
`gammaOne`. -/
theorem firstChern_toTruncated (f : X ⟶ S) (C : ChernComparison f)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    C.toTruncated (firstChernClass f L) = gammaOne f C.chern L := sorry

/-- The canonical de Rham comparison sends the logarithmic first Chern class to the relative
de Rham first Chern class. -/
theorem firstChern_toDeRham (f : X ⟶ S) (C : ChernComparison f)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    C.toDeRhamCohomology (firstChernClass f L) =
      C.chern.deRhamFirstChern (Scheme.Modules.picardClass L) := sorry

/-- The canonical inclusion and Hodge comparison send the logarithmic first Chern class to
the Hodge first Chern class. -/
theorem firstChern_toHodge (f : X ⟶ S) (C : ChernComparison f)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    C.toHodge (firstChernClass f L) =
      C.chern.hodgeFirstChern (Scheme.Modules.picardClass L) := sorry

end LogarithmicForms

end DeRham

end Scheme

end AlgebraicGeometry
