module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_27_1
public import stacks_project.Chap90.Lemma_90_3_4_Length
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap90.Lemma_90_27_7
import Mathlib.Tactic.CrossRefAttribute

/-!
# Minimal smooth prorepresentable presentations

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` admits a
presentation by a minimal smooth prorepresentable groupoid in functors if and
only if it is a deformation category with finite-dimensional tangent space and
infinitesimal automorphism space. A normalized presentation implies this, and
is equivalent when `k / residueImage Λ k` is separable. Minimal presentations
are unique up to isomorphism of groupoids in functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Functor
open ArtinianLocalAlgCat
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- A normalized smooth prorepresentable groupoid in functors on
`ArtinianLocalAlgCat Λ k` is minimal. -/
instance instIsMinimal_of_isNormalized
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsNormalized G] :
    IsMinimal G := sorry

/-- If `Algebra.IsSeparable (Algebra.residueImage Λ k) k`, then a minimal smooth
prorepresentable groupoid in functors on `ArtinianLocalAlgCat Λ k` is
normalized. -/
instance instIsNormalized_of_isMinimal
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k]
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G] :
    IsNormalized G := sorry

/-- Theorem 90.27.8 (1): if `F` is a deformation category over
`ArtinianLocalAlgCat Λ k` whose tangent space
`(fiberIsoClassFunctor F.p).obj (dualNumber Λ k)` and infinitesimal automorphism
space `infinitesimalAutomorphisms F.p` are finite-dimensional over `k`, then `F`
admits a presentation by a minimal smooth prorepresentable groupoid in
functors. -/
@[stacks 06TE]
theorem exists_minimalSmoothProrepresentablePresentation
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [IsDeformationCategory F.p]
    [FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k))]
    [FiniteDimensional k (infinitesimalAutomorphisms F.p)] :
    ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G)
      (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory),
      BasedFunctor.IsEquivalence φ := sorry

/-- Theorem 90.27.8 (1): `F` admits a presentation by a minimal smooth
prorepresentable groupoid in functors on `ArtinianLocalAlgCat Λ k` if and only
if `F.p` is a deformation category whose tangent space
`(fiberIsoClassFunctor F.p).obj (dualNumber Λ k)` and infinitesimal automorphism
space `infinitesimalAutomorphisms F.p` are finite-dimensional over `k`. -/
@[stacks 06TE]
theorem exists_minimalSmoothProrepresentablePresentation_iff
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)) :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G)
      (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory),
      BasedFunctor.IsEquivalence φ) ↔
      ∃ (_ : IsDeformationCategory F.p),
        FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) ∧
          FiniteDimensional k (infinitesimalAutomorphisms F.p) := sorry

/-- Theorem 90.27.8 (1): `F` admits a presentation by a minimal smooth
prorepresentable groupoid in functors on `ArtinianLocalAlgCat Λ k` if and only
if it admits a presentation by a smooth prorepresentable groupoid in functors. -/
@[stacks 06TE]
theorem exists_minimalSmoothProrepresentablePresentation_iff_exists_smooth
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)) :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G)
      (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory),
      BasedFunctor.IsEquivalence φ) ↔
      ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
        (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory),
        IsSmooth G.s G.t ∧ IsProrepresentable G ∧
          BasedFunctor.IsEquivalence φ := sorry

/-- Theorem 90.27.8 (1): a presentation of `F` by a normalized smooth
prorepresentable groupoid in functors on `ArtinianLocalAlgCat Λ k` yields a
presentation by a minimal smooth prorepresentable groupoid in functors. -/
@[stacks 06TE]
theorem exists_minimalSmoothProrepresentablePresentation_of_isNormalized
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k)) :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hNorm : IsNormalized G)
      (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory),
      BasedFunctor.IsEquivalence φ) →
      ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
        (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
        (hMin : IsMinimal G)
        (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory),
        BasedFunctor.IsEquivalence φ := sorry

/-- Theorem 90.27.8 (2): if `Algebra.IsSeparable (Algebra.residueImage Λ k) k`,
then a presentation of `F` by a minimal smooth prorepresentable groupoid in
functors on `ArtinianLocalAlgCat Λ k` yields a presentation by a normalized
smooth prorepresentable groupoid in functors. -/
@[stacks 06TE]
theorem exists_normalizedSmoothProrepresentablePresentation_of_isMinimal
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hMin : IsMinimal G)
      (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory),
      BasedFunctor.IsEquivalence φ) →
      ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
        (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
        (hNorm : IsNormalized G)
        (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory),
        BasedFunctor.IsEquivalence φ := sorry

/-- Theorem 90.27.8 (2): if `Algebra.IsSeparable (Algebra.residueImage Λ k) k`,
then `F` admits a presentation by a normalized smooth prorepresentable groupoid
in functors on `ArtinianLocalAlgCat Λ k` if and only if `F.p` is a deformation
category whose tangent space
`(fiberIsoClassFunctor F.p).obj (dualNumber Λ k)` and infinitesimal automorphism
space `infinitesimalAutomorphisms F.p` are finite-dimensional over `k`. -/
@[stacks 06TE]
theorem exists_normalizedSmoothProrepresentablePresentation_iff
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
      (hSmooth : IsSmooth G.s G.t) (hPro : IsProrepresentable G)
      (hNorm : IsNormalized G)
      (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory),
      BasedFunctor.IsEquivalence φ) ↔
      ∃ (_ : IsDeformationCategory F.p),
        FiniteDimensional k ((fiberIsoClassFunctor F.p).obj (dualNumber Λ k)) ∧
          FiniteDimensional k (infinitesimalAutomorphisms F.p) := sorry

/-- Theorem 90.27.8 (3): the minimal smooth prorepresentable groupoids in
functors which provide a presentation of `F` are unique up to isomorphism. -/
@[stacks 06TE]
theorem nonempty_iso_of_isPresentation
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H]
    (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory)
    (ψ : BasedCategory.ofFunctor H.forget ⥤ᵇ F.toBasedCategory)
    [BasedFunctor.IsEquivalence φ] [BasedFunctor.IsEquivalence ψ] :
    Nonempty (Iso G H) := sorry

end CategoryTheory.GroupoidInFunctors
