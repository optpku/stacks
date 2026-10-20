/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Module

/-!
# Local criteria for pseudo-coherent morphisms

This file relates pseudo-coherence of a scheme morphism to affine-local conditions and to
relative pseudo-coherence of the structure sheaf.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- A scheme morphism is pseudo-coherent if and only if this holds on the section-ring maps
associated to one affine open cover of the target and affine open covers of its pullbacks. -/
theorem pseudoCoherent_iff_exists_affineOpenCover (f : X ⟶ S) :
    AlgebraicGeometry.PseudoCoherent f ↔
      ∃ 𝒱 : S.AffineOpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.IsPseudoCoherentRingMap
                ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom := sorry

/-- A scheme morphism is pseudo-coherent if and only if it is locally of finite type and its
structure sheaf is pseudo-coherent relative to the target. -/
theorem pseudoCoherent_iff_structureSheaf_isPseudoCoherentOver (f : X ⟶ S) :
    AlgebraicGeometry.PseudoCoherent f ↔
      ∃ h_finiteType : LocallyOfFiniteType f,
        @Scheme.Modules.IsPseudoCoherentOver X S
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) f h_finiteType := sorry

/-- Pseudo-coherence on one compatible pair of affine covers, pseudo-coherence on every
compatible pair of affine opens, and local finite type together with relative pseudo-coherence
of the structure sheaf are equivalent. -/
theorem pseudoCoherent_tfae (f : X ⟶ S) :
    List.TFAE [
      ∃ 𝒱 : S.AffineOpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.IsPseudoCoherentRingMap
                ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom,
      ∀ {V : S.Opens}, IsAffineOpen V →
        ∀ {U : X.Opens}, IsAffineOpen U →
          ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.IsPseudoCoherentRingMap (f.appLE V U e).hom,
      ∃ h_finiteType : LocallyOfFiniteType f,
        @Scheme.Modules.IsPseudoCoherentOver X S
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) f h_finiteType
    ] := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.PseudoCoherent

/-- Pseudo-coherence of scheme morphisms is local at the source for the fppf precoverage. -/
instance isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.PseudoCoherent :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.PseudoCoherent
