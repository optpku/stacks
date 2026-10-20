/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Regular.Criteria
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.21.2: for a scheme morphism with locally Noetherian fibres, regularity,
flatness with geometrically regular fibres, affine section-ring regularity, and the two
compatible-cover formulations are equivalent. -/
@[stacks 07R8]
#check
  (AlgebraicGeometry.Scheme.Hom.regular_tfae :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      LocallyNoetherianFibers f →
        List.TFAE [
          Regular f,
          Flat f ∧
            ∀ y : Y,
              Scheme.Hom.IsGeometricallyRegular (f.fiberToSpecResidueField y),
          ∀ {V : Y.Opens}, IsAffineOpen V →
            ∀ {U : X.Opens}, IsAffineOpen U →
              ∀ e : U ≤ f ⁻¹ᵁ V,
                RingHom.Regular (f.appLE V U e).hom,
          ∃ 𝒱 : Y.OpenCover,
            ∀ j : 𝒱.I₀,
              ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
                ∀ i : 𝒰.I₀,
                  Regular (𝒰.f i ≫ 𝒱.pullbackHom f j),
          ∃ 𝒱 : Y.AffineOpenCover,
            ∀ j : 𝒱.I₀,
              ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
                ∀ i : 𝒰.I₀,
                  RingHom.Regular
                    ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom
        ])
