/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import stacks_project.Chap90.Lemma_90_12_2_Tensor

/-!
# Lemma 90.12.4

A morphism of predeformation categories induces a `k`-linear map on tangent
spaces whenever the associated isomorphism-class functors both satisfy (S2).
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [IsPredeformationCategory p] [IsPredeformationCategory q]
variable [HasSchlessingerH2 (fiberIsoClassFunctor p)]
  [HasSchlessingerH2 (fiberIsoClassFunctor q)]

namespace CategoryTheory.BasedFunctor

/-- The map on dual-number fibre isomorphism classes induced by a morphism of predeformation
categories. -/
def differential (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) →
      (fiberIsoClassFunctor q).obj (dualNumber Λ k) :=
  fun x ↦ (φ.fiberFunctor (dualNumber Λ k)).isoClassesMap x

/-- Lemma 90.12.4: let `φ : ℱ ⟶ 𝒢` be a morphism of predeformation categories. If
`ℱ̄` and `𝒢̄` both satisfy (S2), then `dφ : T ℱ → T 𝒢` is `k`-linear. -/
@[stacks 06IJ]
theorem isLinearMap_differential (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    IsLinearMap k (differential φ) := sorry

/-- The differential of a morphism of predeformation categories as a bundled `k`-linear map,
when the associated isomorphism-class functors satisfy (S2). -/
def differentialLinearMap (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    (fiberIsoClassFunctor p).obj (dualNumber Λ k) →ₗ[k]
      (fiberIsoClassFunctor q).obj (dualNumber Λ k) :=
  IsLinearMap.mk' (differential φ) (isLinearMap_differential φ)

/-- The underlying function of `differentialLinearMap φ` is `differential φ`. -/
theorem differentialLinearMap_apply (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : (fiberIsoClassFunctor p).obj (dualNumber Λ k)) :
    differentialLinearMap φ x = differential φ x := sorry

end CategoryTheory.BasedFunctor
