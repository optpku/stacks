/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.IsomorphismFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Flat invariance of base-changed module morphisms

Flat pullback covering the relevant finite-type supports preserves and reflects epimorphy,
monomorphy, vanishing, and invertibility after every base change to a test scheme.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X ⟶ B) (φ : X' ⟶ X) [Flat φ]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)

/-- Epimorphy after base change is preserved and reflected by flat pullback whose image covers
the support of the finite-type codomain. -/
@[stacks 083I]
theorem baseChangeMap_epi_iff_of_flat [𝒢.IsFiniteType]
    (h_support : moduleSupport 𝒢 ⊆ Set.range (Points.map φ)) (T : SchemeOver B) :
    Epi (baseChangeMap f T.hom u) ↔
      Epi (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u)) :=
  sorry

/-- Vanishing after base change is preserved and reflected by flat pullback whose image covers
the support of the finite-type codomain. -/
@[stacks 083I]
theorem baseChangeMap_zero_iff_of_flat_codomain [𝒢.IsFiniteType]
    (h_support : moduleSupport 𝒢 ⊆ Set.range (Points.map φ)) (T : SchemeOver B) :
    baseChangeMap f T.hom u = 0 ↔
      baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u) = 0 :=
  sorry

/-- Monomorphy after base change is preserved and reflected by flat pullback whose image covers
the support of the finite-type domain. -/
@[stacks 083I]
theorem baseChangeMap_mono_iff_of_flat [ℱ.IsFiniteType]
    (h_support : moduleSupport ℱ ⊆ Set.range (Points.map φ)) (T : SchemeOver B) :
    Mono (baseChangeMap f T.hom u) ↔
      Mono (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u)) :=
  sorry

/-- Vanishing after base change is preserved and reflected by flat pullback whose image covers
the support of the finite-type domain. -/
@[stacks 083I]
theorem baseChangeMap_zero_iff_of_flat_domain [ℱ.IsFiniteType]
    (h_support : moduleSupport ℱ ⊆ Set.range (Points.map φ)) (T : SchemeOver B) :
    baseChangeMap f T.hom u = 0 ↔
      baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u) = 0 :=
  sorry

/-- Invertibility after base change is preserved and reflected by flat pullback whose image
covers the supports of the finite-type domain and codomain. -/
@[stacks 083I]
theorem baseChangeMap_isIso_iff_of_flat [ℱ.IsFiniteType] [𝒢.IsFiniteType]
    (h_support : moduleSupport ℱ ∪ moduleSupport 𝒢 ⊆ Set.range (Points.map φ))
    (T : SchemeOver B) :
    IsIso (baseChangeMap f T.hom u) ↔
      IsIso (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u)) :=
  sorry

/-- The isomorphism functors of a module morphism and its flat pullback are nonempty on the
same test schemes when the image covers both finite-type supports. -/
theorem isomorphismFunctor_obj_nonempty_iff_of_flat [ℱ.IsFiniteType] [𝒢.IsFiniteType]
    (h_support : moduleSupport ℱ ∪ moduleSupport 𝒢 ⊆ Set.range (Points.map φ))
    (T : SchemeOver B) :
    Nonempty ((isomorphismFunctor f u).obj (op T)) ↔
      Nonempty ((isomorphismFunctor (φ ≫ f) ((pullback φ).map u)).obj (op T)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
