/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fppf covering families of schemes

This module provides the indexed-family and fixed-target presentations of
covering families for the canonical fppf precoverage.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {ι : Type v}

/-- The map on points induced by an indexed family of schemes over `T`. -/
abbrev fppfCoveringPointMap (family : ι → Over T) : (Σ i, (family i).left) → T :=
  fun p ↦ (family p.1).hom.base p.2

/-- The point map of an indexed fppf family evaluates by its structure map. -/
@[simp]
theorem fppfCoveringPointMap_apply
    (family : ι → Over T) (p : Σ i, (family i).left) :
    fppfCoveringPointMap family p = (family p.1).hom.base p.2 := rfl

/-- An indexed family over `T` is fppf-covering when its arrows form a cover
for the canonical fppf precoverage. -/
abbrev FppfCovering (family : ι → Over T) : Prop :=
  Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
    Scheme.fppfPrecoverage.coverings T

/-- An indexed family is fppf-covering exactly when its arrows generate a
covering presieve for the fppf precoverage. -/
theorem fppfCovering_iff_mem_precoverage (family : ι → Over T) :
    FppfCovering family ↔
      Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        Scheme.fppfPrecoverage.coverings T := Iff.rfl

/-- The pointwise characterization of an fppf covering family. -/
theorem fppfCovering_iff (family : ι → Over T) :
    FppfCovering family ↔
      (∀ i : ι, Flat (family i).hom) ∧
        (∀ i : ι, LocallyOfFinitePresentation (family i).hom) ∧
          Function.Surjective (fppfCoveringPointMap family) := by
  rw [FppfCovering, fppfPrecoverage, ofArrows_mem_precoverage_iff]
  constructor
  · rintro ⟨hcover, hprop⟩
    refine ⟨fun i ↦ (hprop i).1, fun i ↦ (hprop i).2, ?_⟩
    intro x
    obtain ⟨i, y, hy⟩ := hcover x
    exact ⟨⟨i, y⟩, hy⟩
  · rintro ⟨hflat, hlfp, hsurj⟩
    refine ⟨?_, fun i ↦ ⟨hflat i, hlfp i⟩⟩
    intro x
    obtain ⟨⟨i, y⟩, hy⟩ := hsurj x
    exact ⟨i, y, hy⟩

/-- An fppf covering family supplies flatness, local finite presentation, and
joint surjectivity. -/
theorem FppfCovering.source_spec {family : ι → Over T} (h : FppfCovering family) :
    (∀ i : ι, Flat (family i).hom) ∧
      (∀ i : ι, LocallyOfFinitePresentation (family i).hom) ∧
        Function.Surjective (fppfCoveringPointMap family) :=
  (fppfCovering_iff family).mp h

/-- Every member of an fppf covering family is flat. -/
theorem FppfCovering.flat {family : ι → Over T} (h : FppfCovering family) (i : ι) :
    Flat (family i).hom :=
  h.source_spec.1 i

/-- Every member of an fppf covering family is locally of finite presentation. -/
theorem FppfCovering.locallyOfFinitePresentation
    {family : ι → Over T} (h : FppfCovering family) (i : ι) :
    LocallyOfFinitePresentation (family i).hom :=
  h.source_spec.2.1 i

/-- The point map of an fppf covering family is surjective. -/
theorem FppfCovering.surjective_pointMap {family : ι → Over T} (h : FppfCovering family) :
    Function.Surjective (fppfCoveringPointMap family) :=
  h.source_spec.2.2

/-- Every point of the target has a preimage in an fppf covering family. -/
theorem FppfCovering.exists_preimage
    {family : ι → Over T} (h : FppfCovering family) (x : T) :
    ∃ p : Σ i, (family i).left, fppfCoveringPointMap family p = x :=
  h.surjective_pointMap x

/-- The arrows of an fppf covering family generate an fppf covering presieve. -/
theorem FppfCovering.mem_fppf_precoverage {family : ι → Over T} (h : FppfCovering family) :
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      Scheme.fppfPrecoverage.coverings T := h

/-- The arrows of an fppf covering family also form a covering presieve for
the flat precoverage. -/
theorem FppfCovering.mem_flat_precoverage {family : ι → Over T} (h : FppfCovering family) :
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      (Scheme.precoverage (fun {_ _} f ↦ Flat f)).coverings T := by
  rw [FppfCovering, fppfPrecoverage_eq_inf] at h
  exact h.1

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

variable (T : Scheme.{u})

/-- An fppf covering of `T`, represented as a canonical fixed-target
`Scheme.Cover` for the fppf precoverage. -/
abbrev FppfCover (T : Scheme.{u}) :=
  T.Cover Scheme.fppfPrecoverage

namespace FppfCover

/-- The arrows of an fppf cover form a covering family for the canonical fppf
precoverage. -/
theorem mem_fppf_precoverage (𝒰 : FppfCover T) :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fppfPrecoverage.coverings T :=
  𝒰.mem₀

/-- Each member of an fppf covering family is flat. -/
theorem flat (𝒰 : FppfCover T) (i : 𝒰.I₀) :
    Flat (𝒰.f i) :=
  (Scheme.Cover.map_prop (P := @Flat ⊓ @LocallyOfFinitePresentation) 𝒰 i).1

/-- Each member of an fppf covering family is locally of finite presentation. -/
theorem locallyOfFinitePresentation (𝒰 : FppfCover T) (i : 𝒰.I₀) :
    LocallyOfFinitePresentation (𝒰.f i) :=
  (Scheme.Cover.map_prop (P := @Flat ⊓ @LocallyOfFinitePresentation) 𝒰 i).2

/-- The images of an fppf covering family jointly cover its target. -/
theorem cover (𝒰 : FppfCover T) (t : T) :
    ∃ i, t ∈ Set.range (𝒰.f i) :=
  ((Scheme.ofArrows_mem_precoverage_iff (@Flat ⊓ @LocallyOfFinitePresentation)).mp
    (mem_fppf_precoverage T 𝒰)).1 t

/-- The defining flatness, local finite presentation, and cover conditions of
an fppf cover. -/
theorem source_spec (𝒰 : FppfCover T) :
    (∀ i, Flat (𝒰.f i)) ∧
      (∀ i, LocallyOfFinitePresentation (𝒰.f i)) ∧
        (∀ t : T, ∃ i, t ∈ Set.range (𝒰.f i)) :=
  ⟨flat T 𝒰, locallyOfFinitePresentation T 𝒰, cover T 𝒰⟩

/-- Forgetting local finite presentation, an fppf cover is a flat covering
family. -/
theorem mem_flat_precoverage (𝒰 : FppfCover T) :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈
      (Scheme.precoverage (fun {_ _} f ↦ Flat f)).coverings T :=
  (Scheme.ofArrows_mem_precoverage_iff @Flat).mpr ⟨cover T 𝒰, flat T 𝒰⟩

end FppfCover

end AlgebraicGeometry
