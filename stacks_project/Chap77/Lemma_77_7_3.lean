module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.FlatInvariance
import StacksCheckRecall

/-!
# Lemma 77.7.3

In Situation 77.7.1, a flat morphism `φ : X' ⟶ X` whose image covers the relevant
finite-type supports does not change the flattening functors of `u` on `Sch/B`.
The five pointwise criteria below express equality of the associated subterminal functors:
epimorphy gives `F_surj = F'_surj`, monomorphy gives `F_inj = F'_inj`, the two vanishing
criteria give `F_zero = F'_zero`, and invertibility gives `F_iso = F'_iso`.
The final check expresses the invertibility criterion using the existing isomorphism functor.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.7.3: flat pullback covering the finite-type codomain support preserves
and reflects surjectivity after every base change. -/
@[stacks 083I] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_epi_iff_of_flat :
    ∀ {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X ⟶ B) (φ : X' ⟶ X) [Flat φ]
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢) [𝒢.IsFiniteType]
      (h_support : moduleSupport 𝒢 ⊆ Set.range (Points.map φ)) (T : SchemeOver B),
      Epi (baseChangeMap f T.hom u) ↔
      Epi (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u)))

/- Vanishing detected using the codomain support. -/
@[stacks 083I] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_zero_iff_of_flat_codomain :
    ∀ {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X ⟶ B) (φ : X' ⟶ X) [Flat φ]
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢) [𝒢.IsFiniteType]
      (h_support : moduleSupport 𝒢 ⊆ Set.range (Points.map φ)) (T : SchemeOver B),
      baseChangeMap f T.hom u = 0 ↔
      baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u) = 0)

/- Injectivity detected using the domain support. -/
@[stacks 083I] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_mono_iff_of_flat :
    ∀ {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X ⟶ B) (φ : X' ⟶ X) [Flat φ]
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType]
      (h_support : moduleSupport ℱ ⊆ Set.range (Points.map φ)) (T : SchemeOver B),
      Mono (baseChangeMap f T.hom u) ↔
      Mono (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u)))

/- Vanishing detected using the domain support. -/
@[stacks 083I] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_zero_iff_of_flat_domain :
    ∀ {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X ⟶ B) (φ : X' ⟶ X) [Flat φ]
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType]
      (h_support : moduleSupport ℱ ⊆ Set.range (Points.map φ)) (T : SchemeOver B),
      baseChangeMap f T.hom u = 0 ↔
      baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u) = 0)

/- Invertibility detected using both supports. -/
@[stacks 083I] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_isIso_iff_of_flat :
    ∀ {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X ⟶ B) (φ : X' ⟶ X) [Flat φ]
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] [𝒢.IsFiniteType]
      (h_support : moduleSupport ℱ ∪ moduleSupport 𝒢 ⊆ Set.range (Points.map φ))
      (T : SchemeOver B),
      IsIso (baseChangeMap f T.hom u) ↔
      IsIso (baseChangeMap (φ ≫ f) T.hom ((pullback φ).map u)))

/- The same invertibility criterion for the isomorphism functor. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctor_obj_nonempty_iff_of_flat :
    ∀ {S : Scheme.{u}} {X X' B : AlgebraicSpace S} (f : X ⟶ B) (φ : X' ⟶ X) [Flat φ]
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] [𝒢.IsFiniteType]
      (h_support : moduleSupport ℱ ∪ moduleSupport 𝒢 ⊆ Set.range (Points.map φ))
      (T : SchemeOver B),
      Nonempty ((isomorphismFunctor f u).obj (op T)) ↔
      Nonempty ((isomorphismFunctor (φ ≫ f) ((pullback φ).map u)).obj (op T)))

end AlgebraicGeometry.AlgebraicSpace.Modules
