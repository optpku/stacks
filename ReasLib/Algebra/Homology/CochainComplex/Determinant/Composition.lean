/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Module
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.ShortExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of determinant maps for two-term cochain complexes

This leaf owns the source-independent two-term determinant comparison.  The admissibility
predicate records the three degreewise hypotheses used by the Stacks Project, while the
determinant map is the contravariant map on determinant lines.  The chapter entry is therefore a
thin recall of `map_comp` rather than a second chapter-local determinant construction.

@stack 0FJL
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Module.Determinant TensorProduct

universe u v w

namespace CochainComplex.Determinant

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/-! ## Determinant lines -/

/- The determinant line is the two-term map `det(K⁻¹) → det(K⁰)`. -/
/-- The determinant line of a cochain complex supported in degrees `-1` and `0`. -/
@[stacks 0FJJ "determinant line of a two-term complex",
  stacks 0FJL "determinant line of a two-term complex"]
abbrev line (K : Cpx)
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)] : Type _ :=
  det[R](K.X (-1)) →ₗ[R] det[R](K.X 0)

/-! ## Admissibility -/

/-- The differential of a cochain map carries the degree `-1` kernel into the degree `0` kernel. -/
theorem kernelDifferential_mem {K L : Cpx} (a : K ⟶ L)
    (x : LinearMap.ker (a.f (-1)).hom) :
    (K.d (-1) 0).hom x ∈ LinearMap.ker (a.f 0).hom := sorry
-- Proof strategy: evaluate the cochain-map square `a.comm (-1) 0` on `x`;
-- its right-hand side is zero because `x ∈ ker(a⁻¹)`.

/-- The kernel differential of a cochain map in the two-term window. -/
@[stacks 0FJJ "kernel differential of a two-term map",
  stacks 0FJL "kernel differential of a two-term map"]
def kernelDifferential {K L : Cpx} (a : K ⟶ L) :
    LinearMap.ker (a.f (-1)).hom →ₗ[R] LinearMap.ker (a.f 0).hom :=
  LinearMap.codRestrict
    (LinearMap.ker (a.f 0).hom)
    ((K.d (-1) 0).hom.comp (LinearMap.ker (a.f (-1)).hom).subtype)
    (kernelDifferential_mem a)

/-- The three Stacks hypotheses on a morphism of two-term complexes: both components are
surjective and the induced differential on the kernel row is bijective. -/
@[stacks 0FJJ "admissible morphism of two-term complexes",
  stacks 0FJL "admissible morphism of two-term complexes"]
structure IsAdmissible {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    (a : K ⟶ L) : Prop where
  mapNegOne_surjective : Function.Surjective (a.f (-1)).hom
  mapZero_surjective : Function.Surjective (a.f 0).hom
  kernelDifferential_bijective : Function.Bijective (kernelDifferential a)

/-- Admissibility is stable under composition of cochain maps. -/
theorem IsAdmissible.comp {K L M : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [M.IsStrictlyGE (-1)] [M.IsStrictlyLE 0]
    {a : K ⟶ L} {b : L ⟶ M} (ha : IsAdmissible a) (hb : IsAdmissible b) :
    IsAdmissible (a ≫ b) := sorry
-- Proof strategy: compose the two degreewise surjections.  For the kernel
-- differential, prove injectivity by successively applying the injective kernel
-- differentials of `b` and `a`; prove surjectivity by lifting through `b` and
-- correcting the residual kernel term through `a`.

/-- A surjection onto a finite projective module makes its kernel finite. -/
theorem finite_kernel_of_surjective {M N : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Finite R (LinearMap.ker f) := sorry
-- Proof strategy: split `f` using projectivity of `N`, identify `M` with the
-- product of `ker f` and `N`, and transport finiteness to the kernel summand.

/-- A surjection between projective modules makes its kernel projective. -/
theorem projective_kernel_of_surjective {M N : Type*}
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Projective R (LinearMap.ker f) := sorry
-- Proof strategy: split the surjection using projectivity of `N`; the resulting
-- idempotent exhibits `ker f` as a direct summand of the projective module `M`.

/-! ## The canonical map -/

/-- The value of the contravariant determinant map on a determinant-line element.

The two short-exact determinant comparisons are the canonical `tensorIsoOfExact` maps for the
degree `-1` and `0` kernel rows, and the kernel differential contributes the middle determinant
factor.  The local kernel instances are consequences of the admissibility surjections; they are
proof-local data, not global instance owners. -/
@[stacks 0FJJ "value of the determinant comparison",
  stacks 0FJL "value of the determinant comparison"]
noncomputable def apply {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) (φ : line L) : line K :=
  -- Local instance justification (proof-local temporary data): admissibility supplies the
  -- surjection needed to derive finite/projective kernel instances for this map only.
  letI : Module.Finite R (LinearMap.ker (a.f (-1)).hom) :=
    finite_kernel_of_surjective (a.f (-1)).hom ha.mapNegOne_surjective
  -- Local instance justification (proof-local temporary data): the same kernel is a split
  -- summand of the finite-projective source term.
  letI : Module.Projective R (LinearMap.ker (a.f (-1)).hom) :=
    projective_kernel_of_surjective (a.f (-1)).hom ha.mapNegOne_surjective
  -- Local instance justification (proof-local temporary data): the degree `0` admissibility
  -- surjection gives the finite kernel instance used by the second determinant row.
  letI : Module.Finite R (LinearMap.ker (a.f 0).hom) :=
    finite_kernel_of_surjective (a.f 0).hom ha.mapZero_surjective
  -- Local instance justification (proof-local temporary data): the degree `0` kernel is likewise
  -- a split projective summand and must not be installed globally from a proof argument.
  letI : Module.Projective R (LinearMap.ker (a.f 0).hom) :=
    projective_kernel_of_surjective (a.f 0).hom ha.mapZero_surjective
  let kerDet :=
    Module.Determinant.mapIso
      (LinearEquiv.ofBijective (kernelDifferential a) ha.kernelDifferential_bijective)
  let detNeg :=
    Module.Determinant.tensorIsoOfExact
      (LinearMap.ker (a.f (-1)).hom).subtype
      (a.f (-1)).hom
      (LinearMap.ker (a.f (-1)).hom).injective_subtype
      ha.mapNegOne_surjective
      (LinearMap.exact_subtype_ker_map (a.f (-1)).hom)
  let detZero :=
    Module.Determinant.tensorIsoOfExact
      (LinearMap.ker (a.f 0).hom).subtype
      (a.f 0).hom
      (LinearMap.ker (a.f 0).hom).injective_subtype
      ha.mapZero_surjective
      (LinearMap.exact_subtype_ker_map (a.f 0).hom)
  detZero.toLinearMap.comp
    ((TensorProduct.map kerDet.toLinearMap φ).comp detNeg.symm.toLinearMap)

/-- Additivity of the determinant-map value in its determinant-line argument. -/
theorem apply_add {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) (φ ψ : line L) :
    apply a ha (φ + ψ) = apply a ha φ + apply a ha ψ := sorry
-- Proof strategy: unfold `apply`; use additivity of `TensorProduct.map` in the
-- determinant-line map and linearity of the two short-exact comparison maps.

/-- Scalar linearity of the determinant-map value in its determinant-line argument. -/
theorem apply_smul {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) (r : R) (φ : line L) :
    apply a ha (r • φ) = r • apply a ha φ := sorry
-- Proof strategy: unfold `apply`; move the scalar through `TensorProduct.map`
-- and the two linear-equivalence maps, then use `LinearMap.map_smul`.

/-- The contravariant determinant map attached to an admissible cochain map. -/
@[stacks 0FJJ "contravariant determinant map",
  stacks 0FJL "contravariant determinant map"]
noncomputable def map {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) : line L →ₗ[R] line K where
  toFun := apply a ha
  map_add' := apply_add a ha
  map_smul' := apply_smul a ha

/-- The contravariant determinant map of an admissible cochain map is bijective. -/
theorem map_bijective {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) :
    Function.Bijective (map a ha) := sorry
-- Proof strategy: package `apply` as the composite Hom-space equivalence induced
-- by `tensorIsoOfExact` in degrees `-1` and `0` and by `mapIso` for the
-- bijective kernel differential; the underlying map of that equivalence is `map`.

/-- The covariant determinant equivalence attached to an admissible cochain map. -/
@[stacks 0FJJ "covariant determinant equivalence",
  stacks 0FJL "covariant determinant equivalence"]
noncomputable def equiv {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) : line K ≃ₗ[R] line L :=
  (LinearEquiv.ofBijective (map a ha) (map_bijective a ha)).symm

/-- The inverse of the covariant determinant equivalence is the canonical contravariant map. -/
@[simp]
theorem equiv_symm_toLinearMap {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    (a : K ⟶ L) (ha : IsAdmissible a) :
    (equiv a ha).symm.toLinearMap = map a ha := sorry
-- Proof strategy: unfold `equiv` and use the inverse computation rule for
-- `LinearEquiv.ofBijective`; extensionality reduces the claim to its defining
-- left- and right-inverse equations.

/-- The determinant map is multiplicative for composable admissible cochain maps (Lemma 15.123.3,
tag 0FJL). -/
@[stacks 0FJL "Lemma 15.123.3: composition of determinant maps"]
theorem map_comp {K L M : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [M.IsStrictlyGE (-1)] [M.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    [Module.Finite R (M.X (-1))] [Module.Projective R (M.X (-1))]
    [Module.Finite R (M.X 0)] [Module.Projective R (M.X 0)]
    {a : K ⟶ L} {b : L ⟶ M} (ha : IsAdmissible a) (hb : IsAdmissible b) :
    (map a ha).comp (map b hb) = map (a ≫ b) (ha.comp hb) := sorry
-- Proof strategy: form the kernel short exact rows for `a`, `b`, and `a ≫ b`.
-- Apply `Module.Determinant.tensorIsoOfExact` naturality in both degrees and the
-- `Module.Determinant.SubmoduleTower.commutes` coherence theorem to identify the
-- two tensor routes, then use linear-map extensionality.

end CochainComplex.Determinant

end
