/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.RingTheory.RingHom.WeaklyEtale

/-!
# Locality of weakly étale scheme morphisms

This module relates weak étaleness of scheme morphisms to weak étaleness of their maps on
sections and records open-cover, affine-open-cover, and restriction criteria.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- Scheme-theoretic weak étaleness is the property associated to weakly étale ring
homomorphisms. -/
instance instHasRingHomProperty :
    HasRingHomProperty (@AlgebraicGeometry.WeaklyEtale.{u}) RingHom.WeaklyEtale := sorry

end AlgebraicGeometry.WeaklyEtale

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- Weak étaleness of a scheme morphism is equivalent to being locally induced by weakly
étale ring homomorphisms. -/
theorem weaklyEtale_iff_locallyOfType (f : X ⟶ S) :
    WeaklyEtale f ↔ LocallyOfType RingHom.WeaklyEtale f := by
  rw [locallyOfType_iff_affineLocally RingHom.WeaklyEtale f
    RingHom.WeaklyEtale.propertyIsLocal]
  have hP := HasRingHomProperty.eq_affineLocally
    (P := @AlgebraicGeometry.WeaklyEtale.{u})
    (Q := @RingHom.WeaklyEtale.{u, u})
  constructor
  · intro hf
    rw [hP] at hf
    exact hf
  · intro hf
    rw [hP]
    exact hf

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.WeaklyEtale

/-- A weakly étale scheme morphism is locally induced by weakly étale ring homomorphisms. -/
instance instLocallyOfType {X S : Scheme.{u}} (f : X ⟶ S) [WeaklyEtale f] :
    LocallyOfType RingHom.WeaklyEtale f :=
  (AlgebraicGeometry.Scheme.Hom.weaklyEtale_iff_locallyOfType f).mp inferInstance

end AlgebraicGeometry.WeaklyEtale

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- Weak étaleness is detected on every section-ring map induced by compatible affine opens. -/
theorem weaklyEtale_iff_affineOpen_appLE (f : X ⟶ S) :
    WeaklyEtale f ↔
      ∀ {V : S.Opens}, IsAffineOpen V →
        ∀ {U : X.Opens}, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          RingHom.WeaklyEtale (f.appLE V U e).hom := by
  rw [weaklyEtale_iff_locallyOfType,
    locallyOfType_iff_forall_affineOpen_appLE RingHom.WeaklyEtale
      RingHom.WeaklyEtale.propertyIsLocal]

/-- A scheme morphism is weakly étale exactly when it is weakly étale on compatible open
covers of the target and their pullbacks. -/
theorem weaklyEtale_iff_exists_openCover (f : X ⟶ S) :
    WeaklyEtale f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, WeaklyEtale (𝒰.f i ≫ 𝒱.pullbackHom f j) := by
  simpa [weaklyEtale_iff_locallyOfType] using
    (locallyOfType_iff_exists_openCover RingHom.WeaklyEtale
      RingHom.WeaklyEtale.propertyIsLocal (f := f))

/-- A scheme morphism is weakly étale exactly when compatible affine covers induce weakly
étale maps on global sections. -/
theorem weaklyEtale_iff_exists_affineOpenCover (f : X ⟶ S) :
    WeaklyEtale f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            RingHom.WeaklyEtale
                ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom := by
  simpa [weaklyEtale_iff_locallyOfType] using
    (locallyOfType_iff_exists_affineOpenCover RingHom.WeaklyEtale
      RingHom.WeaklyEtale.propertyIsLocal (f := f))

/-- Restricting a weakly étale morphism to compatible open subschemes preserves weak
étaleness. -/
theorem weaklyEtale_resLE {f : X ⟶ S} {V : S.Opens} {U : X.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    WeaklyEtale f → WeaklyEtale (f.resLE V U e) := by
  intro hf
  letI : WeaklyEtale f := hf
  infer_instance

end AlgebraicGeometry.Scheme.Hom
