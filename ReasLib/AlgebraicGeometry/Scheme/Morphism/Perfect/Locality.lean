/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.TorAmplitude
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Composition
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Flat
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.PseudoCoherent
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Locality
public import ReasLib.RingTheory.RingHom.Perfect.Basic

/-!
# Local criteria for perfect morphisms

This file relates perfectness of section-ring maps on an affine cover to perfectness on every
compatible pair of affine opens, and records that perfectness is local at the source for the
fppf precoverage.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- For a locally finite-type morphism, perfectness of the section-ring maps on one compatible
pair of affine covers is equivalent to perfectness on every compatible pair of affine opens. -/
theorem perfect_tfae (f : X ⟶ S) [LocallyOfFiniteType f] :
    List.TFAE [
      ∃ 𝒱 : S.AffineOpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.IsPerfectRingMap
                ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom,
      ∀ {V : S.Opens}, IsAffineOpen V →
        ∀ {U : X.Opens}, IsAffineOpen U →
          ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.IsPerfectRingMap (f.appLE V U e).hom
    ] := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.LocallyOfType

/-- Perfectness of scheme morphisms is local at the source for the fppf precoverage. -/
instance isPerfectRingMap_isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap)
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.LocallyOfType
