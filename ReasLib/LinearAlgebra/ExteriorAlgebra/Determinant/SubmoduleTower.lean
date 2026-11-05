/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.ShortExact
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants of submodule towers

For submodules `K ≤ L ≤ M`, the quotient rows determine four canonical determinant
comparisons. This file exposes the quotient-row maps independently of determinants, the
finite-projective propagation needed by the comparisons, and the coherence of the resulting
determinant square.

@stack 0FJD
-/

@[expose] public section

noncomputable section

universe u v

open scoped Module.Determinant TensorProduct

namespace Module.Projective

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A module is projective when a submodule and the corresponding quotient are projective. -/
@[stacks 0FJD "projectivity from a projective submodule and quotient"]
theorem of_submodule_quotient (N : Submodule R M)
    [Module.Projective R N] [Module.Projective R (M ⧸ N)] :
    Module.Projective R M := sorry
-- Proof strategy: split `N.mkQ` using projectivity of `M ⧸ N`; combine the section with
-- `N.subtype` to identify `M` with `N × (M ⧸ N)`, then transport projectivity across this
-- equivalence and the product instance.

end Module.Projective

namespace Submodule.Tower

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The inclusion of nested submodules followed by the quotient by the smaller submodule is
exact. -/
@[stacks 0FJD "exact row for nested submodules"]
theorem exact_inclusion_mkQ (K L : Submodule R M) (hKL : K ≤ L) :
    Function.Exact (Submodule.inclusion hKL) (K.submoduleOf L).mkQ := sorry
-- Proof strategy: use `Submodule.exact_subtype_mkQ` for `K.submoduleOf L` and identify its subtype
-- map with `Submodule.inclusion hKL` by extensionality.

/-- The submodule of `L` cut out by `K` maps into `K` under the inclusion `L → M`. -/
@[stacks 0FJD "nested-submodule inclusion respects the lower submodule"]
theorem submoduleOf_le_comap_subtype (K L : Submodule R M) (hKL : K ≤ L) :
    K.submoduleOf L ≤ K.comap L.subtype := sorry
-- Proof strategy: unfold membership in `submoduleOf` and `comap`; the required membership is the
-- first component of the subtype witness.

/-- The canonical map `L / K → M / K` for nested submodules `K ≤ L`. -/
@[stacks 0FJD "inclusion in the quotient row of a submodule tower"]
def quotientInclusion (K L : Submodule R M) (hKL : K ≤ L) :
    (L ⧸ K.submoduleOf L) →ₗ[R] M ⧸ K :=
  Submodule.mapQ (K.submoduleOf L) K L.subtype
    (submoduleOf_le_comap_subtype K L hKL)

/-- The identity of `M` carries `K` into `L` when `K ≤ L`. -/
@[stacks 0FJD "identity map respects nested submodules"]
theorem le_comap_id (K L : Submodule R M) (hKL : K ≤ L) :
    K ≤ L.comap (LinearMap.id : M →ₗ[R] M) := by
  intro m hm
  exact hKL hm
-- Proof strategy: intro an element of `K`, simplify membership in the identity comap, and apply
-- `hKL`.

/-- The canonical map `M / K → M / L` for nested submodules `K ≤ L`. -/
@[stacks 0FJD "projection in the quotient row of a submodule tower"]
def quotientProjection (K L : Submodule R M) (hKL : K ≤ L) :
    M ⧸ K →ₗ[R] M ⧸ L :=
  Submodule.mapQ K L LinearMap.id (le_comap_id K L hKL)

/-- The quotient-row inclusion agrees with the evident map on representatives from `L`. -/
@[simp, stacks 0FJD "quotient-row inclusion on representatives"]
theorem quotientInclusion_mkQ (K L : Submodule R M) (hKL : K ≤ L) (x : L) :
    quotientInclusion K L hKL ((K.submoduleOf L).mkQ x) = K.mkQ x := sorry
-- Proof strategy: unfold `quotientInclusion` and apply the computation rule for `Submodule.mapQ`;
-- the subtype map sends `x` to its underlying element of `M`.

/-- The quotient-row projection agrees with the quotient map by `L` on representatives from
`M`. -/
@[simp, stacks 0FJD "quotient-row projection on representatives"]
theorem quotientProjection_mkQ (K L : Submodule R M) (hKL : K ≤ L) (x : M) :
    quotientProjection K L hKL (K.mkQ x) = L.mkQ x := rfl
-- Proof strategy: unfold `quotientProjection`, apply the computation rule for `Submodule.mapQ`,
-- and simplify `LinearMap.id_apply`.

/-- The canonical map `L / K → M / K` is injective. -/
@[stacks 0FJD "injectivity of the quotient-row inclusion"]
theorem quotientInclusion_injective (K L : Submodule R M) (hKL : K ≤ L) :
    Function.Injective (quotientInclusion K L hKL) := sorry
-- Proof strategy: use quotient induction on a representative `x : L`; if its image in `M ⧸ K`
-- vanishes, the quotient-kernel criterion puts `x` in `K.submoduleOf L`, hence its original class
-- is zero.

/-- The canonical map `M / K → M / L` is surjective. -/
@[stacks 0FJD "surjectivity of the quotient-row projection"]
theorem quotientProjection_surjective (K L : Submodule R M) (hKL : K ≤ L) :
    Function.Surjective (quotientProjection K L hKL) := by
  intro y
  obtain ⟨x, rfl⟩ := L.mkQ_surjective y
  exact ⟨K.mkQ x, rfl⟩
-- Proof strategy: lift a target class with `L.mkQ_surjective`, represent it by `x : M`, and use
-- `quotientProjection_mkQ` on the class `K.mkQ x`.

/-- The canonical quotient row `L / K → M / K → M / L` is exact. -/
@[stacks 0FJD "exact quotient row of a submodule tower"]
theorem exact_quotientInclusion_quotientProjection
    (K L : Submodule R M) (hKL : K ≤ L) :
    Function.Exact (quotientInclusion K L hKL) (quotientProjection K L hKL) := sorry
-- Proof strategy: prove both inclusions between the range and kernel using quotient induction;
-- the forward inclusion follows from the representative formulas, while the reverse inclusion
-- lifts a kernel representative lying in `L` through `quotientInclusion`.

/-- Finiteness of `K` and `L / K` implies finiteness of `L`. -/
@[stacks 0FJD "finiteness across the left quotient row"]
theorem finiteMiddle (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R K] [Module.Finite R (L ⧸ K.submoduleOf L)] :
    Module.Finite R L := sorry
-- Proof strategy: apply the standard finite-module extension theorem to the surjection
-- `(K.submoduleOf L).mkQ`, whose kernel is the finite submodule identified with `K` by
-- `Submodule.inclusion hKL` and `exact_inclusion_mkQ`.

/-- Projectivity of `K` and `L / K` implies projectivity of `L`. -/
@[stacks 0FJD "projectivity across the left quotient row"]
theorem projectiveMiddle (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R K] [Module.Projective R (L ⧸ K.submoduleOf L)] :
    Module.Projective R L := sorry
-- Proof strategy: transfer projectivity from `K` to `K.submoduleOf L` along the canonical linear
-- equivalence and apply `Module.Projective.of_submodule_quotient` to that submodule of `L`.

/-- Finiteness of the three graded pieces `K`, `L / K`, and `M / L` implies finiteness of
`M`. -/
@[stacks 0FJD "finiteness of the ambient module from a submodule tower"]
theorem finiteAmbient (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R K] [Module.Finite R (L ⧸ K.submoduleOf L)]
    [Module.Finite R (M ⧸ L)] : Module.Finite R M := sorry
-- Proof strategy: first obtain `Module.Finite R L` from `finiteMiddle`, then apply the finite
-- extension theorem to the canonical exact row `L → M → M ⧸ L`.

/-- Projectivity of the three graded pieces `K`, `L / K`, and `M / L` implies projectivity of
`M`. -/
@[stacks 0FJD "projectivity of the ambient module from a submodule tower"]
theorem projectiveAmbient (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R K] [Module.Projective R (L ⧸ K.submoduleOf L)]
    [Module.Projective R (M ⧸ L)] : Module.Projective R M := sorry
-- Proof strategy: obtain projectivity of `L` from `projectiveMiddle`, then apply
-- `Module.Projective.of_submodule_quotient` to the submodule `L ≤ M`.

/-- Finiteness of `L / K` and `M / L` implies finiteness of `M / K`. -/
@[stacks 0FJD "finiteness across the quotient row of a submodule tower"]
theorem finiteTotalQuotient (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Finite R (L ⧸ K.submoduleOf L)] [Module.Finite R (M ⧸ L)] :
    Module.Finite R (M ⧸ K) := sorry
-- Proof strategy: apply the finite-module extension theorem to the exact quotient row using
-- `quotientInclusion_injective`, `quotientProjection_surjective`, and
-- `exact_quotientInclusion_quotientProjection`.

/-- Projectivity of `L / K` and `M / L` implies projectivity of `M / K`. -/
@[stacks 0FJD "projectivity across the quotient row of a submodule tower"]
theorem projectiveTotalQuotient (K L : Submodule R M) (hKL : K ≤ L)
    [Module.Projective R (L ⧸ K.submoduleOf L)] [Module.Projective R (M ⧸ L)] :
    Module.Projective R (M ⧸ K) := sorry
-- Proof strategy: identify the range of `quotientInclusion` with a submodule linearly equivalent
-- to `L ⧸ K`, identify its quotient with `M ⧸ L` using exactness and surjectivity, and apply
-- `Module.Projective.of_submodule_quotient`.

end Submodule.Tower

namespace Module.Determinant.SubmoduleTower

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (K L : Submodule R M) (hKL : K ≤ L)
variable [Module.Finite R K] [Module.Projective R K]
variable [Module.Finite R (L ⧸ K.submoduleOf L)]
variable [Module.Projective R (L ⧸ K.submoduleOf L)]
variable [Module.Finite R (M ⧸ L)] [Module.Projective R (M ⧸ L)]

/-- The determinant comparison for `0 → K → L → L / K → 0`. -/
@[stacks 0FJD "determinant comparison for the left row of a submodule tower"]
noncomputable def leftIso :
    (det[R](K) ⊗[R] det[R](L ⧸ K.submoduleOf L)) ≃ₗ[R] det[R](L) :=
  -- Local instance justification (proof-local temporary data): the middle term is finite by
  -- the two finite graded pieces of the left row.
  letI : Module.Finite R L := Submodule.Tower.finiteMiddle K L hKL
  -- Local instance justification (proof-local temporary data): the split projective quotient row
  -- canonically supplies projectivity of the middle term.
  letI : Module.Projective R L := Submodule.Tower.projectiveMiddle K L hKL
  Module.Determinant.tensorIsoOfExact
    (Submodule.inclusion hKL) (K.submoduleOf L).mkQ
    (Submodule.inclusion_injective hKL) (K.submoduleOf L).mkQ_surjective
    (Submodule.Tower.exact_inclusion_mkQ K L hKL)

/-- The determinant comparison for `0 → L → M → M / L → 0`. -/
@[stacks 0FJD "determinant comparison for the right row of a submodule tower"]
noncomputable def rightIso :
    (det[R](L) ⊗[R] det[R](M ⧸ L)) ≃ₗ[R] det[R](M) :=
  -- Local instance justification (proof-local temporary data): the left row supplies finiteness
  -- of `L` from its two finite graded pieces.
  letI : Module.Finite R L := Submodule.Tower.finiteMiddle K L hKL
  -- Local instance justification (proof-local temporary data): the left row supplies
  -- projectivity of `L` from its two projective graded pieces.
  letI : Module.Projective R L := Submodule.Tower.projectiveMiddle K L hKL
  -- Local instance justification (proof-local temporary data): all three finite graded pieces
  -- supply finiteness of the ambient module.
  letI : Module.Finite R M := Submodule.Tower.finiteAmbient K L hKL
  -- Local instance justification (proof-local temporary data): all three projective graded pieces
  -- supply projectivity of the ambient module.
  letI : Module.Projective R M := Submodule.Tower.projectiveAmbient K L hKL
  Module.Determinant.tensorIsoOfExact L.subtype L.mkQ Subtype.val_injective
    L.mkQ_surjective (LinearMap.exact_subtype_mkQ L)

/-- The determinant comparison for `0 → K → M → M / K → 0`. -/
@[stacks 0FJD "determinant comparison for the outer row of a submodule tower"]
noncomputable def totalIso :
    (det[R](K) ⊗[R] det[R](M ⧸ K)) ≃ₗ[R] det[R](M) :=
  -- Local instance justification (proof-local temporary data): all three finite graded pieces
  -- supply finiteness of the ambient module.
  letI : Module.Finite R M := Submodule.Tower.finiteAmbient K L hKL
  -- Local instance justification (proof-local temporary data): all three projective graded pieces
  -- supply projectivity of the ambient module.
  letI : Module.Projective R M := Submodule.Tower.projectiveAmbient K L hKL
  -- Local instance justification (proof-local temporary data): the exact quotient row supplies
  -- finiteness of `M / K` from `L / K` and `M / L`.
  letI : Module.Finite R (M ⧸ K) := Submodule.Tower.finiteTotalQuotient K L hKL
  -- Local instance justification (proof-local temporary data): the split exact quotient row
  -- supplies projectivity of `M / K`.
  letI : Module.Projective R (M ⧸ K) :=
    Submodule.Tower.projectiveTotalQuotient K L hKL
  Module.Determinant.tensorIsoOfExact K.subtype K.mkQ Subtype.val_injective
    K.mkQ_surjective (LinearMap.exact_subtype_mkQ K)

/-- The determinant comparison for the canonical quotient row
`0 → L / K → M / K → M / L → 0`. -/
@[stacks 0FJD "determinant comparison for the quotient row of a submodule tower"]
noncomputable def quotientIso :
    (det[R](L ⧸ K.submoduleOf L) ⊗[R] det[R](M ⧸ L)) ≃ₗ[R] det[R](M ⧸ K) :=
  -- Local instance justification (proof-local temporary data): the exact quotient row supplies
  -- finiteness of its middle term from its two finite outer terms.
  letI : Module.Finite R (M ⧸ K) := Submodule.Tower.finiteTotalQuotient K L hKL
  -- Local instance justification (proof-local temporary data): the split exact quotient row
  -- supplies projectivity of its middle term.
  letI : Module.Projective R (M ⧸ K) :=
    Submodule.Tower.projectiveTotalQuotient K L hKL
  Module.Determinant.tensorIsoOfExact
    (Submodule.Tower.quotientInclusion K L hKL)
    (Submodule.Tower.quotientProjection K L hKL)
    (Submodule.Tower.quotientInclusion_injective K L hKL)
    (Submodule.Tower.quotientProjection_surjective K L hKL)
    (Submodule.Tower.exact_quotientInclusion_quotientProjection K L hKL)

/-- The route through `det(L) ⊗ det(M / L)` in the determinant square of a submodule tower. -/
@[stacks 0FJD "upper route in the determinant square of a submodule tower"]
noncomputable def viaMiddle :
    ((det[R](K) ⊗[R] det[R](L ⧸ K.submoduleOf L)) ⊗[R] det[R](M ⧸ L)) →ₗ[R]
      det[R](M) :=
  (rightIso K L hKL).toLinearMap.comp
    (TensorProduct.congr (leftIso K L hKL)
      (LinearEquiv.refl R det[R](M ⧸ L))).toLinearMap

/-- The route through `det(K) ⊗ det(M / K)` in the determinant square of a submodule tower. -/
@[stacks 0FJD "lower route in the determinant square of a submodule tower"]
noncomputable def viaTotalQuotient :
    ((det[R](K) ⊗[R] det[R](L ⧸ K.submoduleOf L)) ⊗[R] det[R](M ⧸ L)) →ₗ[R]
      det[R](M) :=
  (totalIso K L hKL).toLinearMap.comp
    ((TensorProduct.assoc R det[R](K) det[R](L ⧸ K.submoduleOf L) det[R](M ⧸ L)).trans
      (TensorProduct.congr (LinearEquiv.refl R det[R](K))
        (quotientIso K L hKL))).toLinearMap

/-- Lemma 15.119.4: the determinant comparisons attached to the four canonical exact rows of a
finite-projective submodule tower `K ≤ L ≤ M` form a commutative square. -/
@[stacks 0FJD "Lemma 15.119.4: determinant comparison for a submodule tower"]
theorem commutes : viaMiddle K L hKL = viaTotalQuotient K L hKL := sorry
-- Proof strategy: use tensor-product induction and `Module.Determinant.hom_ext`; choose exterior
-- lifts of the two quotient determinant factors, expand the four `tensorIsoOfExact_spec` formulas,
-- and finish by associativity of exterior multiplication and the representative formulas for the
-- quotient-row maps.

/-- The determinant-tower coherence evaluated on a pure tensor of the three graded determinant
lines. -/
@[stacks 0FJD "pointwise determinant coherence for a submodule tower"]
theorem commutes_apply
    (xK : det[R](K)) (xLK : det[R](L ⧸ K.submoduleOf L)) (xML : det[R](M ⧸ L)) :
    viaMiddle K L hKL (xK ⊗ₜ[R] xLK ⊗ₜ[R] xML) =
      viaTotalQuotient K L hKL (xK ⊗ₜ[R] xLK ⊗ₜ[R] xML) := sorry
-- Proof strategy: apply `LinearMap.congr_fun (commutes K L hKL)` to the displayed pure tensor.

end Module.Determinant.SubmoduleTower

end
