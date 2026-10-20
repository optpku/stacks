/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.Restriction

/-!
# Locality of formally smooth scheme morphisms

Formal smoothness of a scheme morphism can be detected on compatible open neighborhoods and
on the induced ring homomorphisms over compatible affine opens and affine open covers.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallySmooth

/-- Formal smoothness of a scheme morphism, formal smoothness on compatible pointwise open
neighborhoods, and formal smoothness of induced ring maps on compatible affine opens or affine
open covers are equivalent. -/
theorem affineOpen_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
    List.TFAE [
      FormallySmooth f,
      ∀ x : X,
        ∃ U : X.Opens, ∃ V : Y.Opens,
          ∃ (hx : x ∈ U) (e : U ≤ f ⁻¹ᵁ V),
            FormallySmooth (f.resLE V U e),
      ∀ {V : Y.Opens}, IsAffineOpen V →
        ∀ {U : X.Opens}, IsAffineOpen U →
          ∀ e : U ≤ f ⁻¹ᵁ V,
            (f.appLE V U e).hom.FormallySmooth,
      ∃ 𝒱 : Y.AffineOpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom.FormallySmooth
    ] := sorry

end AlgebraicGeometry.FormallySmooth
