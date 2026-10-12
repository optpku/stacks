/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_15_2
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# Lemma 77.7.3

In Situation 77.7.1, a flat morphism `φ : X' ⟶ X` whose image covers the relevant
finite-type supports does not change the flattening functors of `u` on `Sch/B`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X ⟶ B) (φ : X' ⟶ X) [Flat φ]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)

/-- Lemma 77.7.3 (1): In Situation 77.7.1, if `φ : X' ⟶ X` is flat, `𝒢` is of finite type,
and `moduleSupport 𝒢 ⊆ Set.range (Points.map φ)`, then `Epi (baseChangeMap f T.hom u)` if and
only if `Epi (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u))`. This is the equality
`F_surj = F'_surj` of the corresponding subterminal functors on `Sch/B`. -/
@[stacks 083I]
theorem baseChangeMap_epi_iff_of_flat [𝒢.IsFiniteType]
    (h_support : moduleSupport 𝒢 ⊆ Set.range (Points.map φ)) (T : SchemeOver B) :
    Epi (baseChangeMap f T.hom u) ↔
      Epi (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u)) :=
  sorry

/-- Lemma 77.7.3 (2): In Situation 77.7.1, if `φ : X' ⟶ X` is flat, `𝒢` is of finite type,
and `moduleSupport 𝒢 ⊆ Set.range (Points.map φ)`, then `baseChangeMap f T.hom u = 0` if and
only if `baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u) = 0`. This is the equality
`F_zero = F'_zero` of the corresponding subterminal functors on `Sch/B`. -/
@[stacks 083I]
theorem baseChangeMap_zero_iff_of_flat_codomain [𝒢.IsFiniteType]
    (h_support : moduleSupport 𝒢 ⊆ Set.range (Points.map φ)) (T : SchemeOver B) :
    baseChangeMap f T.hom u = 0 ↔
      baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u) = 0 :=
  sorry

/-- Lemma 77.7.3 (3): In Situation 77.7.1, if `φ : X' ⟶ X` is flat, `ℱ` is of finite type,
and `moduleSupport ℱ ⊆ Set.range (Points.map φ)`, then `Mono (baseChangeMap f T.hom u)` if and
only if `Mono (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u))`. This is the equality
`F_inj = F'_inj` of the corresponding subterminal functors on `Sch/B`. -/
@[stacks 083I]
theorem baseChangeMap_mono_iff_of_flat [ℱ.IsFiniteType]
    (h_support : moduleSupport ℱ ⊆ Set.range (Points.map φ)) (T : SchemeOver B) :
    Mono (baseChangeMap f T.hom u) ↔
      Mono (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u)) :=
  sorry

/-- Lemma 77.7.3 (4): In Situation 77.7.1, if `φ : X' ⟶ X` is flat, `ℱ` is of finite type,
and `moduleSupport ℱ ⊆ Set.range (Points.map φ)`, then `baseChangeMap f T.hom u = 0` if and
only if `baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u) = 0`. This is the equality
`F_zero = F'_zero` of the corresponding subterminal functors on `Sch/B`. -/
@[stacks 083I]
theorem baseChangeMap_zero_iff_of_flat_domain [ℱ.IsFiniteType]
    (h_support : moduleSupport ℱ ⊆ Set.range (Points.map φ)) (T : SchemeOver B) :
    baseChangeMap f T.hom u = 0 ↔
      baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u) = 0 :=
  sorry

/-- Lemma 77.7.3 (5): In Situation 77.7.1, if `φ : X' ⟶ X` is flat, `ℱ` and `𝒢` are of finite
type, and `moduleSupport ℱ ∪ moduleSupport 𝒢 ⊆ Set.range (Points.map φ)`, then
`IsIso (baseChangeMap f T.hom u)` if and only if
`IsIso (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u))`. This is the equality
`F_iso = F'_iso` of the corresponding subterminal functors on `Sch/B`. -/
@[stacks 083I]
theorem baseChangeMap_isIso_iff_of_flat [ℱ.IsFiniteType] [𝒢.IsFiniteType]
    (h_support : moduleSupport ℱ ∪ moduleSupport 𝒢 ⊆ Set.range (Points.map φ))
    (T : SchemeOver B) :
    IsIso (baseChangeMap f T.hom u) ↔
      IsIso (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u)) :=
  sorry

/-- Pointwise, `isomorphismFunctor f u` and `isomorphismFunctor (φ ≫ f) ((pullback φ).map u)`
are nonempty on the same objects of `SchemeOver B` under the finite-type support-covering
hypotheses of `baseChangeMap_isIso_iff_of_flat`. -/
theorem isomorphismFunctor_obj_nonempty_iff_of_flat [ℱ.IsFiniteType] [𝒢.IsFiniteType]
    (h_support : moduleSupport ℱ ∪ moduleSupport 𝒢 ⊆ Set.range (Points.map φ))
    (T : SchemeOver B) :
    Nonempty ((isomorphismFunctor f u).obj (op T)) ↔
      Nonempty ((isomorphismFunctor (φ ≫ f) ((pullback φ).map u)).obj (op T)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
