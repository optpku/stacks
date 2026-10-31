/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Quasi-finite scheme morphisms

This file owns the global quasi-finite condition for scheme morphisms. Mathlib's
`LocallyQuasiFinite` records the finite-fibre condition but deliberately does not include local
finite type, so the global notion combines it with the project-level `FiniteType` owner.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme morphism is quasi-finite at a point in the finite-type sense when it is both of
finite type and stalkwise quasi-finite there. -/
def FiniteType.QuasiFiniteAt (x : X) : Prop :=
  f.FiniteTypeAt x ∧ f.QuasiFiniteAt x

/-- Finite-type quasi-finiteness at a point is the conjunction of its two defining conditions. -/
theorem FiniteType.QuasiFiniteAt.iff_finiteTypeAt_and_quasiFiniteAt (x : X) :
    FiniteType.QuasiFiniteAt f x ↔ f.FiniteTypeAt x ∧ f.QuasiFiniteAt x := Iff.rfl

/-- Finite-type quasi-finiteness at a point is characterized on compatible affine neighborhoods
by a finite-type ring map that is quasi-finite at the corresponding prime. -/
theorem FiniteType.QuasiFiniteAt.iff_exists_affineNeighborhood (x : X) :
    FiniteType.QuasiFiniteAt f x ↔
      ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens),
        ∃ V : S.affineOpens, ∃ e : U ≤ f ⁻¹ᵁ V,
          (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType ∧
            (CommRingCat.Hom.hom (f.appLE V U e)).QuasiFiniteAt
              (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := by
  constructor
  · rintro ⟨⟨U, hxU, V, e, hft⟩, hqf⟩
    exact ⟨U, hxU, V, e, hft, hqf.quasiFiniteAt U.2 V.2 e hxU⟩
  · rintro ⟨U, hxU, V, e, hft, hqf⟩
    refine ⟨⟨U, hxU, V, e, hft⟩, ?_⟩
    change (f.stalkMap x).hom.QuasiFinite
    refine RingHom.QuasiFinite.of_comp
      (g := (S.presheaf.germ V (f x) (e hxU)).hom) ?_
    rw [← CommRingCat.hom_comp, f.germ_stalkMap,
      ← X.presheaf.germ_res (homOfLE e) _ hxU,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc, CommRingCat.hom_comp]
    algebraize [(f.appLE V U e).hom, (X.presheaf.germ U x hxU).hom,
      (X.presheaf.germ U x hxU).hom.comp (f.appLE V U e).hom]
    have := U.2.isLocalization_stalk ⟨x, hxU⟩
    have : Algebra.QuasiFinite Γ(S, V)
        (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) := hqf
    rw [RingHom.QuasiFinite]
    exact (Algebra.QuasiFinite.iff_of_algEquiv
      ((IsLocalization.algEquiv (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
        (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal)
        (X.presheaf.stalk x)).restrictScalars Γ(S, V))).mp this

/-- Local finite type together with local quasi-finiteness is equivalent to finite-type
quasi-finiteness at every source point. -/
@[stacks 01TD]
theorem FiniteType.locallyQuasiFinite_iff_forall_quasiFiniteAt :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∀ x : X, FiniteType.QuasiFiniteAt f x := by
  have hft := HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType) (f := f)
    (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).left
  constructor
  · rintro ⟨hlft, hlqf⟩ x
    haveI := hlqf
    obtain ⟨V, U, hxU, e, hU⟩ := hft.mp hlft x
    exact ⟨⟨U, hxU, V, e, hU⟩, f.quasiFiniteAt x⟩
  · intro h
    have hlft : LocallyOfFiniteType f := hft.mpr fun x ↦ by
      obtain ⟨U, hxU, V, e, hU⟩ := (h x).1
      exact ⟨V, U, hxU, e, hU⟩
    haveI := hlft
    refine ⟨hlft, locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr ?_⟩
    intro s
    rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
    rintro ⟨x, hx⟩
    have hx : f x = s := hx
    subst s
    have hopen := Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (h x).2
    simpa [Set.image_singleton, Scheme.Hom.asFiber] using
      (f.fiberHomeo (f x)).isOpen_image.mpr hopen

/-- A scheme morphism is quasi-finite when it is of finite type and locally quasi-finite. -/
@[stacks 01TD]
class QuasiFinite : Prop extends FiniteType f, LocallyQuasiFinite f

/-- Finite type together with local quasi-finiteness canonically supplies quasi-finiteness. -/
instance instQuasiFinite [FiniteType f] [LocallyQuasiFinite f] :
    QuasiFinite f where
  toFiniteType := inferInstance
  toLocallyQuasiFinite := inferInstance

/-- A quasi-finite morphism is of finite type. -/
instance instFiniteTypeOfQuasiFinite [QuasiFinite f] :
    FiniteType f := QuasiFinite.toFiniteType

/-- A quasi-finite morphism is quasi-compact. -/
instance instQuasiCompactOfQuasiFinite [QuasiFinite f] :
    QuasiCompact f := (QuasiFinite.toFiniteType (f := f)).toQuasiCompact

/-- A quasi-finite morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeOfQuasiFinite [QuasiFinite f] :
    LocallyOfFiniteType f := (QuasiFinite.toFiniteType (f := f)).toLocallyOfFiniteType

/-- A quasi-finite morphism satisfies mathlib's local quasi-finiteness condition. -/
instance instLocallyQuasiFiniteOfQuasiFinite [QuasiFinite f] :
    LocallyQuasiFinite f := QuasiFinite.toLocallyQuasiFinite

/-- Quasi-finite structures are proposition-valued. -/
instance instSubsingletonQuasiFinite :
    Subsingleton (QuasiFinite f) := inferInstance

/-- The defining condition for a quasi-finite scheme morphism. -/
@[stacks 01TD]
theorem quasiFinite_iff :
    QuasiFinite f ↔ FiniteType f ∧ LocallyQuasiFinite f := by
  constructor
  · intro hf
    exact ⟨hf.toFiniteType, hf.toLocallyQuasiFinite⟩
  · rintro ⟨hft, hlqf⟩
    exact { toFiniteType := hft, toLocallyQuasiFinite := hlqf }

/-- A morphism is quasi-finite exactly when it is of finite type and every source point is
isolated in its fibre. -/
theorem quasiFinite_iff_finiteType_and_isOpen_singleton_asFiber :
    QuasiFinite f ↔
      FiniteType f ∧ ∀ x : X, IsOpen ({f.asFiber x} : Set (f.fiber (f x))) := by
  constructor
  · intro hf
    haveI := hf
    exact ⟨hf.toFiniteType, fun x ↦
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (f.quasiFiniteAt x)⟩
  · rintro ⟨hft, h⟩
    haveI := hft
    have hlqf := (FiniteType.locallyQuasiFinite_iff_forall_quasiFiniteAt f).mpr fun x ↦ by
      obtain ⟨V, U, hxU, e, hU⟩ :=
        (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType) (f := f)
          (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
            RingHom.finiteType_holdsForLocalizationAway).left).mp inferInstance x
      exact ⟨⟨U, hxU, V, e, hU⟩,
        Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (h x)⟩
    exact { toFiniteType := hft, toLocallyQuasiFinite := hlqf.2 }

/-- A quasi-finite morphism is equivalently quasi-compact, locally of finite type, and locally
quasi-finite in mathlib's finite-fibre sense. -/
@[stacks 01TJ]
theorem quasiFinite_iff_quasiCompact_locallyOfFiniteType_and_locallyQuasiFinite :
    QuasiFinite f ↔
      QuasiCompact f ∧ LocallyOfFiniteType f ∧ LocallyQuasiFinite f := by
  constructor
  · intro hf
    exact ⟨hf.toFiniteType.toQuasiCompact, hf.toFiniteType.toLocallyOfFiniteType,
      hf.toLocallyQuasiFinite⟩
  · rintro ⟨hqc, hlft, hlqf⟩
    exact
      { toFiniteType := { toQuasiCompact := hqc, toLocallyOfFiniteType := hlft }
        toLocallyQuasiFinite := hlqf }

/-- Construct a quasi-finite morphism from its quasi-compact, local finite-type, and local
quasi-finiteness components. -/
theorem quasiFinite_of_quasiCompact_of_locallyOfFiniteType_of_locallyQuasiFinite
    (hqc : QuasiCompact f) (hlft : LocallyOfFiniteType f) (hlqf : LocallyQuasiFinite f) :
    QuasiFinite f :=
  { toFiniteType := { toQuasiCompact := hqc, toLocallyOfFiniteType := hlft }
    toLocallyQuasiFinite := hlqf }

/-- Every point of a quasi-finite morphism is a quasi-finite point. -/
theorem quasiFiniteAt_of_quasiFinite [QuasiFinite f] (x : X) :
    f.QuasiFiniteAt x := f.quasiFiniteAt x

/-- Every point of a quasi-finite morphism is a quasi-finite point. -/
theorem QuasiFinite.quasiFiniteAt (hf : QuasiFinite f) (x : X) :
    f.QuasiFiniteAt x := by
  haveI := hf
  exact f.quasiFiniteAt x

/-- A quasi-finite morphism is quasi-compact and quasi-finite at every source point. -/
theorem QuasiFinite.quasiCompact_and_forall_quasiFiniteAt (hf : QuasiFinite f) :
    QuasiCompact f ∧ ∀ x : X, f.QuasiFiniteAt x :=
  ⟨hf.toFiniteType.toQuasiCompact, fun x ↦ hf.quasiFiniteAt f x⟩

/-- A quasi-finite morphism is locally of finite type. -/
theorem QuasiFinite.locallyOfFiniteType (hf : QuasiFinite f) :
    LocallyOfFiniteType f := hf.toFiniteType.toLocallyOfFiniteType

/-- A quasi-finite morphism is quasi-compact. -/
theorem QuasiFinite.quasiCompact (hf : QuasiFinite f) :
    QuasiCompact f := hf.toFiniteType.toQuasiCompact

/-- A quasi-finite morphism has finite fibres over all target points. -/
@[stacks 02NH]
theorem QuasiFinite.finiteFibers (hf : QuasiFinite f) :
    ∀ s : S, Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S)) := by
  haveI := hf
  exact f.finite_preimage_singleton

/-- Local finite type, quasi-compactness, and finite fibres imply quasi-finiteness. -/
@[stacks 02NH]
theorem quasiFinite_of_locallyOfFiniteType_of_quasiCompact_of_finiteFibers
    (hlft : LocallyOfFiniteType f) (hqc : QuasiCompact f)
    (hfib : ∀ s : S, Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S))) :
    QuasiFinite f := by
  haveI := hlft
  exact
    { toFiniteType := { toQuasiCompact := hqc, toLocallyOfFiniteType := hlft }
      toLocallyQuasiFinite := LocallyQuasiFinite.of_finite_preimage_singleton f hfib }

end Scheme.Hom
end AlgebraicGeometry
