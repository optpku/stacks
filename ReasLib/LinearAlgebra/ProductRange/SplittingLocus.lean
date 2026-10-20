/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.EpiMono
public import ReasLib.LinearAlgebra.LinearMap.CoefficientIdeal
public import ReasLib.LinearAlgebra.ProductRange

/-!
# The product-splitting locus of a split linear map

For a split map into a binary product, a chosen retraction determines two projectors of the
source.  The two cross-coordinate maps measure whether the image is a product of submodules.
Their coefficient ideals define a closed splitting locus, independent of the chosen retraction.
@stack 0F80
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace LinearMap.ProductRange

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N₁ : Type v} [AddCommGroup N₁] [Module R N₁]
variable {N₂ : Type v} [AddCommGroup N₂] [Module R N₂]

/-- The endomorphism of the source obtained by projecting to the first target factor and then
using a chosen retraction. -/
@[stacks 0F80 "first splitting projector"]
def fstProjector (s : M →ₗ[R] N₁ × N₂) (r : N₁ × N₂ →ₗ[R] M) : M →ₗ[R] M :=
  (r.comp (LinearMap.inl R N₁ N₂)).comp ((LinearMap.fst R N₁ N₂).comp s)

/-- The endomorphism of the source obtained by projecting to the second target factor and then
using a chosen retraction. -/
@[stacks 0F80 "second splitting projector"]
def sndProjector (s : M →ₗ[R] N₁ × N₂) (r : N₁ × N₂ →ₗ[R] M) : M →ₗ[R] M :=
  (r.comp (LinearMap.inr R N₁ N₂)).comp ((LinearMap.snd R N₁ N₂).comp s)

/-- The first target coordinate contributed by the second projector. -/
@[stacks 0F80 "first cross-coordinate map"]
def fstCross (s : M →ₗ[R] N₁ × N₂) (r : N₁ × N₂ →ₗ[R] M) : M →ₗ[R] N₁ :=
  ((LinearMap.fst R N₁ N₂).comp s).comp (sndProjector s r)

/-- The second target coordinate contributed by the first projector. -/
@[stacks 0F80 "second cross-coordinate map"]
def sndCross (s : M →ₗ[R] N₁ × N₂) (r : N₁ × N₂ →ₗ[R] M) : M →ₗ[R] N₂ :=
  ((LinearMap.snd R N₁ N₂).comp s).comp (fstProjector s r)

/-- A split pair-valued map has product-shaped image exactly when its two cross-coordinate maps
vanish. -/
theorem identifiesWithProdSubmodules_iff_cross_eq_zero
    (s : M →ₗ[R] N₁ × N₂) (r : N₁ × N₂ →ₗ[R] M)
    (hr : r.comp s = LinearMap.id) :
    s.identifiesWithProdSubmodules ↔ fstCross s r = 0 ∧ sndCross s r = 0 := sorry

/-- After arbitrary extension of scalars, product-shaped image is equivalent to vanishing of the
base changes of the two cross-coordinate maps. -/
theorem baseChangeIdentifiesWithProdSubmodules_iff_cross_eq_zero
    (s : M →ₗ[R] N₁ × N₂) (r : N₁ × N₂ →ₗ[R] M)
    (hr : r.comp s = LinearMap.id)
    (S : Type*) [CommRing S] [Algebra R S] :
    s.baseChangeIdentifiesWithProdSubmodules S ↔
      (fstCross s r).baseChange S = 0 ∧ (sndCross s r).baseChange S = 0 := sorry

/-- The ideal cutting out the locus where a split pair-valued map has product-shaped image. -/
@[stacks 0F80 "product-splitting ideal"]
def splittingIdeal (s : M →ₗ[R] N₁ × N₂) (r : N₁ × N₂ →ₗ[R] M) : Ideal R :=
  coefficientIdeal (fstCross s r) + coefficientIdeal (sndCross s r)

/-- A retraction of a pair-valued linear map, recorded at the linear-map level. -/
@[stacks 0F80 "linear retraction of a product-valued map"]
def Retraction (s : M →ₗ[R] N₁ × N₂) :=
  { r : N₁ × N₂ →ₗ[R] M // r.comp s = LinearMap.id }

/-- The canonical product-splitting locus ideal, defined as the infimum of the splitting ideals
attached to all retractions.  If no retraction exists, this has the standard empty-infimum value
`⊤`. -/
@[stacks 0F80 "canonical product-splitting locus ideal"]
def locusIdeal (s : M →ₗ[R] N₁ × N₂) : Ideal R :=
  ⨅ r : Retraction s, splittingIdeal s r.1

/-- The splitting ideal is finitely generated when the source is finite and both targets are
projective. -/
theorem splittingIdeal_fg [Module.Finite R M]
    [Module.Projective R N₁] [Module.Projective R N₂]
    (s : M →ₗ[R] N₁ × N₂) (r : N₁ × N₂ →ₗ[R] M) :
    (splittingIdeal s r).FG := sorry

/-- An algebra kills the splitting ideal exactly when the corresponding base-changed map has
product-shaped image. -/
theorem splittingIdeal_le_ker_iff
    [Module.Projective R N₁] [Module.Projective R N₂]
    (s : M →ₗ[R] N₁ × N₂) (r : N₁ × N₂ →ₗ[R] M)
    (hr : r.comp s = LinearMap.id)
    (S : Type*) [CommRing S] [Algebra R S] :
    splittingIdeal s r ≤ RingHom.ker (algebraMap R S) ↔
      s.baseChangeIdentifiesWithProdSubmodules S := sorry

/-- For a split map, the splitting ideal is independent of the chosen retraction. -/
theorem splittingIdeal_eq
    [Module.Projective R N₁] [Module.Projective R N₂]
    (s : M →ₗ[R] N₁ × N₂) (r r' : N₁ × N₂ →ₗ[R] M)
    (hr : r.comp s = LinearMap.id) (hr' : r'.comp s = LinearMap.id) :
    splittingIdeal s r = splittingIdeal s r' := sorry

/-- For a split map with projective targets, the canonical locus ideal agrees with the ideal
computed from any displayed retraction. -/
theorem locusIdeal_eq_splittingIdeal
    [Module.Projective R N₁] [Module.Projective R N₂]
    (s : M →ₗ[R] N₁ × N₂) (r : N₁ × N₂ →ₗ[R] M)
    (hr : r.comp s = LinearMap.id) :
    locusIdeal s = splittingIdeal s r := sorry

/-- For a split map with projective targets, an algebra kills the canonical locus ideal exactly
when the base-changed map has product-shaped image. -/
theorem locusIdeal_le_ker_iff
    [Module.Projective R N₁] [Module.Projective R N₂]
    (s : M →ₗ[R] N₁ × N₂) (hs : IsSplitMono (ModuleCat.ofHom s))
    (S : Type*) [CommRing S] [Algebra R S] :
    locusIdeal s ≤ RingHom.ker (algebraMap R S) ↔
      s.baseChangeIdentifiesWithProdSubmodules S := sorry

/-- The canonical product-splitting locus ideal is finitely generated for a split map from a
finite module to a product of projective modules. -/
theorem locusIdeal_fg
    [Module.Finite R M] [Module.Projective R N₁] [Module.Projective R N₂]
    (s : M →ₗ[R] N₁ × N₂) (hs : IsSplitMono (ModuleCat.ofHom s)) :
    (locusIdeal s).FG := sorry

/-- A split map from a finite module to a product of projective modules has a finitely generated
ideal which universally cuts out its product-splitting locus. -/
theorem exists_fgIdeal_of_finite_source
    [Module.Finite R M] [Module.Projective R N₁] [Module.Projective R N₂]
    (s : M →ₗ[R] N₁ × N₂) (hs : IsSplitMono (ModuleCat.ofHom s)) :
    ∃ J : Ideal R, J.FG ∧
      ∀ (S : Type*) [CommRing S] [Algebra R S],
        J ≤ RingHom.ker (algebraMap R S) ↔
          s.baseChangeIdentifiesWithProdSubmodules S := sorry

/-- Stacks Project, Lemma 15.97.7 (Tag 0F80): the product-splitting locus of a split injection
between finite projective modules is cut out by a finitely generated ideal. -/
@[stacks 0F80 "product-splitting locus of a split injection"]
theorem exists_fgIdeal
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N₁] [Module.Projective R N₁]
    [Module.Finite R N₂] [Module.Projective R N₂]
    (s : M →ₗ[R] N₁ × N₂) (hs : IsSplitMono (ModuleCat.ofHom s)) :
    ∃ J : Ideal R, J.FG ∧
      ∀ (S : Type*) [CommRing S] [Algebra R S],
        J ≤ RingHom.ker (algebraMap R S) ↔
          s.baseChangeIdentifiesWithProdSubmodules S := sorry

end LinearMap.ProductRange
