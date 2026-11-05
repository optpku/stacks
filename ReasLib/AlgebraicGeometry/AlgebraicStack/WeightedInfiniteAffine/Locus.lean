/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine.Action

/-!
# Loci of the weighted infinite affine stratification

The finite locus kills the first `i` coordinates and inverts `x_i`; the infinite
locus kills every coordinate. These schemes represent the invariant strata.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine

/-- The index set `ℕ ∪ {∞}` of the weighted gerbe stratification. -/
inductive StratumIndex where
  /-- Finite index `i` for the stratum `𝒳_i`. -/
  | ofNat (i : ℕ)
  /-- The infinite index for the origin stratum `𝒳_∞`. -/
  | inf

/-- The vanishing ideal `(x_0, …, x_{i-1})` of the first `i` coordinates. -/
def vanishingIdeal (k : Type u) [Field k] (i : ℕ) : Ideal (coordRing k) :=
  Ideal.span (Set.image (MvPolynomial.X : ℕ → coordRing k) (Set.Iio i))

/-- The closed subscheme ring `k[x_j | j : ℕ] / (x_0, …, x_{i-1})`. -/
abbrev finiteClosedRing (k : Type u) [Field k] (i : ℕ) : Type u :=
  coordRing k ⧸ vanishingIdeal k i

/-- The locally closed stratum ring of `𝒳_i`, obtained by inverting the image of `x_i`. -/
abbrev finiteLocusRing (k : Type u) [Field k] (i : ℕ) : Type u :=
  Localization.Away (Ideal.Quotient.mk (vanishingIdeal k i) (MvPolynomial.X i))

/-- The structure map from `k` to the finite-stratum ring. -/
def finiteLocusAlgebraMap (k : Type u) [Field k] (i : ℕ) :
    k →+* finiteLocusRing k i :=
  algebraMap k (finiteLocusRing k i)

/-- The canonical map from the coordinate ring to the finite-stratum ring. -/
def finiteLocusFromCoord (k : Type u) [Field k] (i : ℕ) :
    coordRing k →+* finiteLocusRing k i :=
  algebraMap (coordRing k) (finiteLocusRing k i)

/-- The locally closed locus of `𝒳_i` as a scheme over `Spec k`. -/
def finiteLocus (k : Type u) [Field k] (i : ℕ) : Over (base k) :=
  OverSpec.affine (CommRingCat.ofHom (finiteLocusAlgebraMap k i))

/-- The underlying scheme of `finiteLocus k i` is `Spec` of the inverted quotient. -/
theorem finiteLocus_left (k : Type u) [Field k] (i : ℕ) :
    (finiteLocus k i).left = Spec (CommRingCat.of (finiteLocusRing k i)) := sorry

/-- Compatibility of `finiteLocusFromCoord` with the maps from `k`. -/
theorem finiteLocusι_w (k : Type u) [Field k] (i : ℕ) :
    Spec.map (CommRingCat.ofHom (finiteLocusFromCoord k i)) ≫ (affineSpace k).hom =
      (finiteLocus k i).hom := sorry

/-- The locally closed immersion of the `𝒳_i` locus into infinite affine space. -/
def finiteLocusι (k : Type u) [Field k] (i : ℕ) : finiteLocus k i ⟶ affineSpace k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (finiteLocusFromCoord k i)))
    (finiteLocusι_w k i)

/-- The underlying scheme map of `finiteLocusι` is `Spec` of `finiteLocusFromCoord`. -/
theorem finiteLocusι_left (k : Type u) [Field k] (i : ℕ) :
    (finiteLocusι k i).left = Spec.map (CommRingCat.ofHom (finiteLocusFromCoord k i)) := sorry

/-- The vanishing ideal of all coordinates, cutting out the origin. -/
def infinityIdeal (k : Type u) [Field k] : Ideal (coordRing k) :=
  Ideal.span (Set.range (MvPolynomial.X : ℕ → coordRing k))

/-- The origin ring `k[x_i | i : ℕ] / (x_i | i : ℕ)`. -/
abbrev infinityLocusRing (k : Type u) [Field k] : Type u :=
  coordRing k ⧸ infinityIdeal k

/-- The structure map from `k` to the origin ring. -/
def infinityLocusAlgebraMap (k : Type u) [Field k] : k →+* infinityLocusRing k :=
  algebraMap k (infinityLocusRing k)

/-- The origin locus `𝒳_∞` as a scheme over `Spec k`. -/
def infinityLocus (k : Type u) [Field k] : Over (base k) :=
  OverSpec.affine (CommRingCat.ofHom (infinityLocusAlgebraMap k))

/-- The underlying scheme of `infinityLocus k` is `Spec` of the origin ring. -/
theorem infinityLocus_left (k : Type u) [Field k] :
    (infinityLocus k).left = Spec (CommRingCat.of (infinityLocusRing k)) := sorry

/-- Compatibility of the origin closed immersion with the maps from `k`. -/
theorem infinityLocusι_w (k : Type u) [Field k] :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal k))) ≫
        (affineSpace k).hom =
      (infinityLocus k).hom := sorry

/-- The closed immersion of the origin into infinite affine space. -/
def infinityLocusι (k : Type u) [Field k] : infinityLocus k ⟶ affineSpace k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal k))))
    (infinityLocusι_w k)

/-- The underlying scheme map of `infinityLocusι` is `Spec` of the quotient map. -/
theorem infinityLocusι_left (k : Type u) [Field k] :
    (infinityLocusι k).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal k))) := sorry

/-- The representing `𝔾ₘ`-invariant locus of a stratum, as a scheme over `Spec k`. -/
def locus (k : Type u) [Field k] (i : StratumIndex) : Over (base k) :=
  match i with
  | StratumIndex.ofNat n => finiteLocus k n
  | StratumIndex.inf => infinityLocus k

/-- The locally closed immersion of a stratum locus into infinite affine space. -/
def locusι (k : Type u) [Field k] (i : StratumIndex) : locus k i ⟶ affineSpace k :=
  match i with
  | StratumIndex.ofNat n => finiteLocusι k n
  | StratumIndex.inf => infinityLocusι k

/-- `locus` on a finite index is `finiteLocus`. -/
theorem locus_finite (k : Type u) [Field k] (i : ℕ) :
    locus k (StratumIndex.ofNat i) = finiteLocus k i := sorry

/-- `locus` at infinity is `infinityLocus`. -/
theorem locus_infinity (k : Type u) [Field k] :
    locus k StratumIndex.inf = infinityLocus k := sorry

/-- On the locus of `𝒳_i`, the coordinate `x_i` is a unit. -/
theorem finiteLocus_X_isUnit (k : Type u) [Field k]
    (i : ℕ) : IsUnit (finiteLocusFromCoord k i (MvPolynomial.X i)) := sorry

/-- On the locus of `𝒳_i`, the coordinates `x_0, …, x_{i-1}` vanish. -/
theorem finiteLocus_X_eq_zero (k : Type u) [Field k]
    (i : ℕ) (j : ℕ) (hj : j < i) : finiteLocusFromCoord k i (MvPolynomial.X j) = 0 := sorry

/-- The infinite stratum `𝒳_∞` is cut out on `U` by the vanishing of every `x_j`. -/
theorem infinityLocus_X_eq_zero (k : Type u) [Field k] :
    ∀ j : ℕ, Ideal.Quotient.mk (infinityIdeal k) (MvPolynomial.X j) = 0 := sorry

/-- Each finite stratum locus is a reduced scheme. -/
instance instIsReducedFiniteLocus (k : Type u) [Field k] (i : ℕ) :
    AlgebraicGeometry.IsReduced (finiteLocus k i).left := sorry

/-- The origin locus is a reduced scheme. -/
instance instIsReducedInfinityLocus (k : Type u) [Field k] :
    AlgebraicGeometry.IsReduced (infinityLocus k).left := sorry

/-- The representing locus of every stratum is a reduced scheme. -/
instance instIsReducedLocus (k : Type u) [Field k] (i : StratumIndex) :
    AlgebraicGeometry.IsReduced (locus k i).left := sorry

end AlgebraicGeometry.AlgebraicStack.WeightedInfiniteAffine
