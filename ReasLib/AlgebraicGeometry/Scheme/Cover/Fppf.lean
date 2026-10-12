/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    fppfCoveringPointMap family p = (family p.1).hom.base p.2 := sorry

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
        Scheme.fppfPrecoverage.coverings T := sorry

/-- The pointwise characterization of an fppf covering family. -/
theorem fppfCovering_iff (family : ι → Over T) :
    FppfCovering family ↔
      (∀ i : ι, Flat (family i).hom) ∧
        (∀ i : ι, LocallyOfFinitePresentation (family i).hom) ∧
          Function.Surjective (fppfCoveringPointMap family) := sorry

/-- An fppf covering family supplies flatness, local finite presentation, and
joint surjectivity. -/
theorem FppfCovering.source_spec {family : ι → Over T} (h : FppfCovering family) :
    (∀ i : ι, Flat (family i).hom) ∧
      (∀ i : ι, LocallyOfFinitePresentation (family i).hom) ∧
        Function.Surjective (fppfCoveringPointMap family) := sorry

/-- Every member of an fppf covering family is flat. -/
theorem FppfCovering.flat {family : ι → Over T} (h : FppfCovering family) (i : ι) :
    Flat (family i).hom := sorry

/-- Every member of an fppf covering family is locally of finite presentation. -/
theorem FppfCovering.locallyOfFinitePresentation
    {family : ι → Over T} (h : FppfCovering family) (i : ι) :
    LocallyOfFinitePresentation (family i).hom := sorry

/-- The point map of an fppf covering family is surjective. -/
theorem FppfCovering.surjective_pointMap {family : ι → Over T} (h : FppfCovering family) :
    Function.Surjective (fppfCoveringPointMap family) := sorry

/-- Every point of the target has a preimage in an fppf covering family. -/
theorem FppfCovering.exists_preimage
    {family : ι → Over T} (h : FppfCovering family) (x : T) :
    ∃ p : Σ i, (family i).left, fppfCoveringPointMap family p = x := sorry

/-- The arrows of an fppf covering family generate an fppf covering presieve. -/
theorem FppfCovering.mem_fppf_precoverage {family : ι → Over T} (h : FppfCovering family) :
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      Scheme.fppfPrecoverage.coverings T := sorry

/-- The arrows of an fppf covering family also form a covering presieve for
the flat precoverage. -/
theorem FppfCovering.mem_flat_precoverage {family : ι → Over T} (h : FppfCovering family) :
    Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
      (Scheme.precoverage (fun {_ _} f ↦ Flat f)).coverings T := sorry

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
    Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fppfPrecoverage.coverings T := sorry

/-- Each member of an fppf covering family is flat. -/
theorem flat (𝒰 : FppfCover T) (i : 𝒰.I₀) :
    Flat (𝒰.f i) := sorry

/-- Each member of an fppf covering family is locally of finite presentation. -/
theorem locallyOfFinitePresentation (𝒰 : FppfCover T) (i : 𝒰.I₀) :
    LocallyOfFinitePresentation (𝒰.f i) := sorry

/-- The images of an fppf covering family jointly cover its target. -/
theorem cover (𝒰 : FppfCover T) (t : T) :
    ∃ i, t ∈ Set.range (𝒰.f i) := sorry

/-- The defining flatness, local finite presentation, and cover conditions of
an fppf cover. -/
theorem source_spec (𝒰 : FppfCover T) :
    (∀ i, Flat (𝒰.f i)) ∧
      (∀ i, LocallyOfFinitePresentation (𝒰.f i)) ∧
        (∀ t : T, ∃ i, t ∈ Set.range (𝒰.f i)) := sorry

/-- Forgetting local finite presentation, an fppf cover is a flat covering
family. -/
theorem mem_flat_precoverage (𝒰 : FppfCover T) :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈
      (Scheme.precoverage (fun {_ _} f ↦ Flat f)).coverings T := sorry

end FppfCover

end AlgebraicGeometry
