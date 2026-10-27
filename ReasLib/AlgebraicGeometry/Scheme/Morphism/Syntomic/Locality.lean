/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme morphism is syntomic if and only if all of its induced ring maps between affine
open subschemes are syntomic. -/
theorem syntomic_iff_affineOpen_appLE_syntomic :
    Syntomic f ↔
      ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
          RingHom.Syntomic ((f.appLE V U e).hom) := sorry

/-- A scheme morphism is syntomic if and only if the target has an open cover whose pullbacks
have open covers by schemes syntomic over the corresponding target pieces. -/
theorem syntomic_iff_exists_openCover_preimageOpenCover :
    Syntomic f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, Syntomic ((𝒰.f i) ≫ (𝒱.pullbackHom f j)) := sorry

/-- A scheme morphism is syntomic if and only if the target has an affine open cover whose
pullbacks have affine open covers on which the induced maps on global sections are syntomic. -/
theorem syntomic_iff_exists_affineOpenCover_preimageAffineOpenCover :
    Syntomic f ↔
      ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u},
          ∀ i : 𝒰.I₀,
            RingHom.Syntomic ((((𝒰.f i) ≫ (𝒱.openCover.pullbackHom f j)).appTop).hom) := sorry

/-- Restricting a syntomic scheme morphism to compatible open subschemes is syntomic. -/
theorem syntomic_resLE_of_syntomic
    (hsyntomic : Syntomic f) {U : X.Opens} {V : S.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    Syntomic (f.resLE V U e) := sorry

end AlgebraicGeometry.Scheme.Hom
