module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.PushforwardStructure
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Module.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.Functor.Derived.Exact

/-!
# Derived modules over a pushed-forward structure sheaf

This file defines the derived category with quasicoherent cohomology over a pushed-forward
structure sheaf and the restriction-of-scalars functor to the base scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X S : Scheme.{u}}

/-- The full subcategory of derived modules over `f_*𝒪_X` whose cohomology sheaves are
quasicoherent. -/
abbrev PushforwardQCoh (f : X ⟶ S) :=
  DerivedCategory.CohomologyIn
    (RingedSpace.quasiCoherentModuleProperty
      (RingedSpace.Hom.PushforwardStructure.target f.toShHom))

/-- Derived restriction of scalars from modules over `f_*𝒪_X` to modules over `𝒪_S`. -/
noncomputable abbrev pushforwardQCohRestrictionDerived (f : X ⟶ S) :
    RingedSpace.ModuleDerived (RingedSpace.Hom.PushforwardStructure.target f.toShHom) ⥤
      RingedSpace.ModuleDerived S.toRingedSpace :=
  let α := RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom
  -- Local instance justification (defeq pin): `mapDerivedCategory` requires the canonical exact restriction-of-scalars finite-limit witness.
  letI : Limits.PreservesFiniteLimits (restrictionAlong.{u, u, u, u} α) :=
    (restrictionAlong_exact.{u, u, u, u, u, u} α).1
  -- Local instance justification (defeq pin): `mapDerivedCategory` requires the canonical exact restriction-of-scalars finite-colimit witness.
  letI : Limits.PreservesFiniteColimits (restrictionAlong.{u, u, u, u} α) :=
    (restrictionAlong_exact.{u, u, u, u, u, u} α).2
  -- Local instance justification (defeq pin): `restrictionAlong` exposes the pushed-forward ring-sheaf presentation while the source uses its ringed-space owner.
  letI : HasDerivedCategory.{u + 1}
      (ringedSiteModuleCategory.{u, u, u, u} (Opens.grothendieckTopology S)
        ((TopCat.Sheaf.pushforward CommRingCat f.toShHom.hom.base).obj X.sheaf)) :=
    RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory.{u, u, u, u} _ _
  -- Local instance justification (defeq pin): `restrictionAlong` exposes the base ring-sheaf presentation while the target uses its ringed-space owner.
  letI : HasDerivedCategory.{u + 1}
      (ringedSiteModuleCategory.{u, u, u, u} (Opens.grothendieckTopology S) S.sheaf) :=
    RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory.{u, u, u, u} _ _
  (restrictionAlong.{u, u, u, u} α).mapDerivedCategory

namespace pushforwardQCohRestrictionDerived

/-- Derived restriction of scalars from `f_*𝒪_X` to `𝒪_S` preserves quasicoherent
cohomology for a quasi-compact, quasi-separated morphism. -/
theorem mapsTo (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty
          (RingedSpace.Hom.PushforwardStructure.target f.toShHom)) ≤
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty S.toRingedSpace)).inverseImage
          (pushforwardQCohRestrictionDerived f) := sorry

end pushforwardQCohRestrictionDerived

/-- Restriction of scalars along `𝒪_S ⟶ f_*𝒪_X`, restricted to derived modules with
quasicoherent cohomology. -/
noncomputable def pushforwardQCohRestriction
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    PushforwardQCoh f ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty S.toRingedSpace) :=
  FullSubcategory.restrict
    (pushforwardQCohRestrictionDerived f)
    (pushforwardQCohRestrictionDerived.mapsTo f)

namespace pushforwardQCohRestriction

/-- Restriction of scalars from derived modules over `f_*𝒪_X` with quasicoherent cohomology
reflects isomorphisms. -/
instance reflectsIsomorphisms (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    (pushforwardQCohRestriction f).ReflectsIsomorphisms := sorry

end pushforwardQCohRestriction

/-- The underived direct image `f_*𝒪_X`, placed in degree zero, has quasicoherent
cohomology for a quasi-compact, quasi-separated morphism. -/
theorem pushforwardStructureSheaf_mem (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    Scheme.ModuleDerived.quasicoherentProperty S
      ((DerivedCategory.singleFunctor S.toRingedSpace.Modules 0).obj
        ((RingedSpace.Hom.pushforward f.toShHom).obj
          (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))) := sorry

/-- The underived direct image `f_*𝒪_X`, placed in degree zero as a derived module
with quasicoherent cohomology. -/
noncomputable def pushforwardStructureSheaf (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] : Scheme.ModuleDerived.Quasicoherent S :=
  ⟨(DerivedCategory.singleFunctor S.toRingedSpace.Modules 0).obj
      ((RingedSpace.Hom.pushforward f.toShHom).obj
        (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)),
    pushforwardStructureSheaf_mem f⟩

/-- The underlying derived module of `pushforwardStructureSheaf f` is the underived
direct image `f_*𝒪_X`, placed in degree zero. -/
@[simp]
theorem pushforwardStructureSheaf_obj (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    (pushforwardStructureSheaf f).obj =
      (DerivedCategory.singleFunctor S.toRingedSpace.Modules 0).obj
        ((RingedSpace.Hom.pushforward f.toShHom).obj
          (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
