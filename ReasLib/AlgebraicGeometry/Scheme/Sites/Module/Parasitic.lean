module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.OverStructurePresheaf

/-!
# Parasitic presheaves of modules

This module defines two objectwise vanishing properties for presheaves of
modules on the standard big sites over a scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace PresheafOfModules

variable {S : Scheme.{u}}

/-- A module presheaf over `S` is parasitic one when it vanishes on every
scheme flat over `S`. -/
def IsParasiticOne
    (ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf)) : Prop :=
  ∀ U : Over S, Flat U.hom → IsZero (ℱ.obj (op U))

/-- The objectwise characterization of a parasitic-one module presheaf. -/
theorem isParasiticOne_iff
    (ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf)) :
    IsParasiticOne ℱ ↔
      ∀ U : Over S, Flat U.hom → IsZero (ℱ.obj (op U)) := sorry

namespace IsParasiticOne

/-- A parasitic-one module presheaf vanishes on a specified flat scheme over
the base. -/
theorem isZero
    {ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf)}
    (hℱ : IsParasiticOne ℱ) (U : Over S) (hU : Flat U.hom) :
    IsZero (ℱ.obj (op U)) := sorry

end IsParasiticOne

/-- The parasitic-one property is invariant under isomorphism of module
presheaves. -/
theorem isParasiticOne_iff_of_iso
    {ℱ 𝒢 : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf)}
    (e : ℱ ≅ 𝒢) : IsParasiticOne ℱ ↔ IsParasiticOne 𝒢 := sorry

/-- A module presheaf over `S` is parasitic for `τ` when it vanishes on every
member of every `τ`-cover of `S`. -/
def IsParasitic
    (ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf))
    (τ : StandardTopology) : Prop :=
  ∀ (𝒰 : Scheme.Cover.{u} τ.precoverage S) (i : 𝒰.I₀),
    IsZero (ℱ.obj (op (Over.mk (𝒰.f i))))

/-- The covering-family characterization of a parasitic module presheaf. -/
theorem isParasitic_iff
    (ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf))
    (τ : StandardTopology) :
    IsParasitic ℱ τ ↔
      ∀ (𝒰 : Scheme.Cover.{u} τ.precoverage S) (i : 𝒰.I₀),
        IsZero (ℱ.obj (op (Over.mk (𝒰.f i)))) := sorry

namespace IsParasitic

/-- A parasitic module presheaf vanishes on a specified member of a
`τ`-cover of the base. -/
theorem isZero
    {ℱ : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf)}
    {τ : StandardTopology} (hℱ : IsParasitic ℱ τ)
    (𝒰 : Scheme.Cover.{u} τ.precoverage S) (i : 𝒰.I₀) :
    IsZero (ℱ.obj (op (Over.mk (𝒰.f i)))) := sorry

end IsParasitic

/-- The parasitic property for `τ` is invariant under isomorphism of module
presheaves. -/
theorem isParasitic_iff_of_iso
    {ℱ 𝒢 : PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf)}
    (τ : StandardTopology) (e : ℱ ≅ 𝒢) :
    IsParasitic ℱ τ ↔ IsParasitic 𝒢 τ := sorry

end PresheafOfModules
