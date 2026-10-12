/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subobject
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.RegularMeromorphicSection
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Denominator ideals of regular meromorphic sections

A meromorphic section of an invertible module determines an ideal of local
functions whose product with the section is regular.  This module realizes
that ideal as a categorical pullback and records its geometric properties.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The meromorphic extension of an `𝒪_X`-module, restricted back to an
`𝒪_X`-module. -/
noncomputable abbrev restrictedMeromorphicSectionSheaf (ℒ : X.Modules) : X.Modules :=
  (restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
    (X.toLocallyRingedSpace.meromorphicSectionSheaf ℒ)

/-- The scalar-extension unit from an `𝒪_X`-module to its restricted
meromorphic extension. -/
noncomputable def meromorphicSectionUnit (ℒ : X.Modules) :
    ℒ ⟶ restrictedMeromorphicSectionSheaf ℒ :=
  (extendRestrictAdj X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).unit.app ℒ ≫
    (restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).map
      ((pullbackExtendIso
        X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).inv.app ℒ)

/-- An invertible `𝒪_X`-module embeds into its restricted meromorphic
extension. -/
@[instance]
theorem meromorphicSectionUnit_mono
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    Mono (meromorphicSectionUnit ℒ) := sorry

/-- The subobject of a restricted meromorphic extension consisting of regular
sections of the original module. -/
noncomputable def regularSectionSubobject
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    Subobject (restrictedMeromorphicSectionSheaf ℒ) :=
  Subobject.mk (meromorphicSectionUnit ℒ)

/-- The morphism `𝒪_X ⟶ ℒ ⊗ 𝒦_X`, restricted to `𝒪_X`-modules, induced by a
meromorphic section of `ℒ`. -/
noncomputable def restrictedMeromorphicSectionMap
    (ℒ : X.Modules)
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      restrictedMeromorphicSectionSheaf ℒ :=
  meromorphicSectionUnit (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≫
    (restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).map
      (SheafOfModules.pullbackObjUnitToUnit
        X.toLocallyRingedSpace.toMeromorphicFunctionRingSheafMap) ≫
    (restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).map
      (X.toLocallyRingedSpace.meromorphicSectionMap ℒ s)

/-- The denominator ideal of a meromorphic section, obtained by pulling regular
sections back along multiplication by the section. -/
noncomputable def denominatorIdealSheaf
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) :
    Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (Subobject.pullback (restrictedMeromorphicSectionMap ℒ s)).obj
    (regularSectionSubobject ℒ)

/-- Multiplication by a meromorphic section on its denominator ideal, with
values in the original module. -/
noncomputable def denominatorSectionMap
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) :
    Subobject.underlying.obj (denominatorIdealSheaf ℒ s) ⟶ ℒ :=
  Subobject.pullbackπ (restrictedMeromorphicSectionMap ℒ s)
      (regularSectionSubobject ℒ) ≫
    (Subobject.underlyingIso (meromorphicSectionUnit ℒ)).hom

/-- A map from an ideal subobject to `ℒ` is multiplication by `s` on exactly
the denominator ideal when it forms the defining pullback square. -/
abbrev IsDenominatorSectionMap
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (ℒ : X.Modules)
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (sectionMap : Subobject.underlying.obj I ⟶ ℒ) : Prop :=
  IsPullback sectionMap I.arrow (meromorphicSectionUnit ℒ)
    (restrictedMeromorphicSectionMap ℒ s)

/-- The canonical denominator section map exhibits the denominator ideal as
the defining pullback. -/
theorem denominatorSectionMap_isPullback
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) :
    IsDenominatorSectionMap (denominatorIdealSheaf ℒ s) ℒ s
      (denominatorSectionMap ℒ s) := sorry

/-- A local function belongs to the denominator ideal exactly when its product
with the meromorphic section comes from a regular local section of `ℒ`. -/
theorem denominatorIdealSheaf_mem_iff
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (V : X.Opens)
    (f : (SheafOfModules.unit X.ringCatSheaf).val.obj (op V)) :
    f ∈ SheafOfModules.Subobject.sections (denominatorIdealSheaf ℒ s) (op V) ↔
      (restrictedMeromorphicSectionMap ℒ s).val.app (op V) f ∈
        SheafOfModules.Subobject.sections (regularSectionSubobject ℒ) (op V) := sorry

/-- The module underlying the denominator ideal of a regular meromorphic
section is quasi-coherent. -/
theorem denominatorIdealModule_isQuasicoherent
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    (Subobject.underlying.obj (denominatorIdealSheaf ℒ s)).IsQuasicoherent := sorry

/-- Multiplication by a regular meromorphic section is a monomorphism on its
denominator ideal. -/
theorem denominatorSectionMap_mono
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    Mono (denominatorSectionMap ℒ s) := sorry

/-- The cokernel of the denominator-ideal inclusion has closed nowhere-dense
support. -/
theorem denominatorIdealSheafArrow_cokernel_hasClosedNowhereDenseSupport
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    IsClosed (SheafOfModules.support (cokernel (denominatorIdealSheaf ℒ s).arrow)) ∧
      IsNowhereDense
        (SheafOfModules.support (cokernel (denominatorIdealSheaf ℒ s).arrow)) := sorry

/-- The cokernel of multiplication by a regular meromorphic section on its
denominator ideal has closed nowhere-dense support. -/
theorem denominatorSectionMap_cokernel_hasClosedNowhereDenseSupport
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    IsClosed (SheafOfModules.support (cokernel (denominatorSectionMap ℒ s))) ∧
      IsNowhereDense
        (SheafOfModules.support (cokernel (denominatorSectionMap ℒ s))) := sorry

/-- The denominator ideal, its multiplication map, and their geometric
properties for a meromorphic section of an invertible module. -/
structure RegularMeromorphicSectionIdealSheaf
    (ℒ : X.Modules)
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) where
  /-- The ideal of local functions whose product with `s` is regular. -/
  denominatorIdeal : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)
  /-- Multiplication by `s` from the denominator ideal to `ℒ`. -/
  sectionMap : Subobject.underlying.obj denominatorIdeal ⟶ ℒ
  /-- The ideal and section map satisfy the defining pullback property. -/
  sectionMap_isPullback :
    IsDenominatorSectionMap denominatorIdeal ℒ s sectionMap
  /-- The module underlying the denominator ideal is quasi-coherent. -/
  idealModule_isQuasicoherent :
    (Subobject.underlying.obj denominatorIdeal).IsQuasicoherent
  /-- Multiplication by `s` on the denominator ideal is a monomorphism. -/
  sectionMap_mono : Mono sectionMap
  /-- The cokernel of the ideal inclusion has closed nowhere-dense support. -/
  inclusionCokernel_hasClosedNowhereDenseSupport :
    IsClosed (SheafOfModules.support (cokernel denominatorIdeal.arrow)) ∧
      IsNowhereDense (SheafOfModules.support (cokernel denominatorIdeal.arrow))
  /-- The cokernel of multiplication by `s` has closed nowhere-dense support. -/
  sectionMapCokernel_hasClosedNowhereDenseSupport :
    IsClosed (SheafOfModules.support (cokernel sectionMap)) ∧
      IsNowhereDense (SheafOfModules.support (cokernel sectionMap))

namespace RegularMeromorphicSectionIdealSheaf

/-- The denominator ideal subobject carried by the result. -/
abbrev idealSheaf
    {ℒ : X.Modules}
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    (h : RegularMeromorphicSectionIdealSheaf ℒ s) :
    Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  h.denominatorIdeal

/-- The module underlying the denominator ideal carried by the result. -/
abbrev idealModule
    {ℒ : X.Modules}
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    (h : RegularMeromorphicSectionIdealSheaf ℒ s) : X.Modules :=
  Subobject.underlying.obj h.idealSheaf

/-- The canonical inclusion of the denominator ideal into `𝒪_X`. -/
abbrev idealSheafArrow
    {ℒ : X.Modules}
    {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    (h : RegularMeromorphicSectionIdealSheaf ℒ s) :
    h.idealModule ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  h.idealSheaf.arrow

/-- The defining pullback, quasi-coherence, injectivity, and support properties
of a regular meromorphic section's denominator ideal. -/
theorem spec
    {ℒ : X.Modules} {s : X.toLocallyRingedSpace.meromorphicSections ℒ}
    (h : RegularMeromorphicSectionIdealSheaf ℒ s) :
    IsDenominatorSectionMap h.idealSheaf ℒ s h.sectionMap ∧
      h.idealModule.IsQuasicoherent ∧
      Mono h.idealSheafArrow ∧
      Mono h.sectionMap ∧
      (∃ T : Set X,
        IsClosed T ∧ IsNowhereDense T ∧
          SheafOfModules.supportedOn T (cokernel h.idealSheafArrow)) ∧
      ∃ T : Set X,
        IsClosed T ∧ IsNowhereDense T ∧
          SheafOfModules.supportedOn T (cokernel h.sectionMap) := sorry

end RegularMeromorphicSectionIdealSheaf

/-- The concrete denominator-ideal result attached to a regular meromorphic
section of an invertible module. -/
noncomputable def regularMeromorphicSectionIdealSheaf
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    RegularMeromorphicSectionIdealSheaf ℒ s :=
  { denominatorIdeal := denominatorIdealSheaf ℒ s
    sectionMap := denominatorSectionMap ℒ s
    sectionMap_isPullback := denominatorSectionMap_isPullback ℒ s
    idealModule_isQuasicoherent := denominatorIdealModule_isQuasicoherent ℒ s hs
    sectionMap_mono := denominatorSectionMap_mono ℒ s hs
    inclusionCokernel_hasClosedNowhereDenseSupport :=
      denominatorIdealSheafArrow_cokernel_hasClosedNowhereDenseSupport ℒ s hs
    sectionMapCokernel_hasClosedNowhereDenseSupport :=
      denominatorSectionMap_cokernel_hasClosedNowhereDenseSupport ℒ s hs }

end AlgebraicGeometry.Scheme
