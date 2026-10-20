/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Criteria for quasi-compact scheme morphisms
-/

@[expose] public section

noncomputable section

open CategoryTheory Topology
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A morphism is quasi-compact exactly when its pullbacks to a fixed affine open cover are
compact schemes. -/
@[stacks 01K4 "fixed affine-cover criterion for quasi-compactness"]
theorem quasiCompact_iff_pullback_compactSpace
    (𝒰 : S.OpenCover) [∀ i, IsAffine (𝒰.X i)] :
    QuasiCompact f ↔ ∀ i, CompactSpace ((𝒰.pullback₁ f).X i) := sorry

/-- A morphism is quasi-compact exactly when this holds on some affine open cover of the target. -/
@[stacks 01K4]
theorem quasiCompact_iff_exists_affineOpenCover :
    QuasiCompact f ↔
      ∃ 𝒰 : Scheme.AffineOpenCover.{v} S,
        ∀ i : 𝒰.I₀, CompactSpace ((𝒰.openCover.pullback₁ f).X i) := sorry

/-- The image of a quasi-compact scheme morphism is closed when stable under specialization. -/
@[stacks 05JL "closed image from stability under specialization"]
theorem isClosed_range_of_stableUnderSpecialization [QuasiCompact f]
    (h : StableUnderSpecialization (Set.range f.base)) :
    IsClosed (Set.range f.base) := sorry

/-- For a quasi-compact scheme morphism, its image is closed exactly when stable under
specialization. -/
@[stacks 05JL]
theorem isClosed_range_iff_stableUnderSpecialization [QuasiCompact f] :
    IsClosed (Set.range f.base) ↔ StableUnderSpecialization (Set.range f.base) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.QuasiCompact

/-- A quasi-compact composite with surjective left factor has quasi-compact right factor. -/
@[stacks 04ZD]
theorem of_comp_surjective
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [Surjective f] (hfg : QuasiCompact (f ≫ g)) : QuasiCompact g := by
  constructor
  intro U hU hU'
  have hpre : IsCompact ((f ≫ g) ⁻¹' U) :=
    hfg.isCompact_preimage U hU hU'
  have himage : f '' ((f ≫ g) ⁻¹' U) = g ⁻¹' U := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq]
    exact f.surjective
  rw [← himage]
  exact hpre.image f.continuous

end AlgebraicGeometry.QuasiCompact
