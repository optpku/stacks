module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.ExteriorPower.LeftTensor

/-!
# Koszul complexes of linear forms

This file owns the Koszul chain complex attached to a linear form on an arbitrary module.  The
finite-family presentation and regularity predicates live in separate leaves.

@stack 0622
@stack 0626
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory ExteriorAlgebra exteriorPower

variable {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]

/-- Contraction by a linear form lowers the exterior-power degree by one. -/
theorem contractLeft_mem_exteriorPower (φ : E →ₗ[R] R) (n : ℕ) (x : ExteriorAlgebra R E)
    (hx : x ∈ ⋀[R]^(n + 1) E) :
    CliffordAlgebra.contractLeft φ x ∈ ⋀[R]^n E := sorry

namespace CliffordAlgebra

/-- Contraction kills a pure exterior monomial when the linear form vanishes on every factor. -/
@[stacks 0622 "contraction vanishes on a zero family"]
theorem contractLeft_ιMulti_eq_zero
    (φ : E →ₗ[R] R) :
    ∀ {n : ℕ} (v : Fin n → E), (∀ k, φ (v k) = 0) →
      contractLeft φ (ExteriorAlgebra.ιMulti R n v) = 0 := sorry

/-- Contraction by `φ` is the unique linear endomorphism of the exterior algebra that vanishes
on scalars and satisfies the odd Leibniz recursion on degree-one generators. -/
@[stacks 0622 "(2), uniqueness of the Koszul differential"]
theorem contractLeft_unique (φ : E →ₗ[R] R)
    (d : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E)
    (h_scalar : ∀ r : R, d (algebraMap R (ExteriorAlgebra R E) r) = 0)
    (h_generator : ∀ (e : E) (x : ExteriorAlgebra R E),
      d (ExteriorAlgebra.ι R e * x) =
        φ e • x - ExteriorAlgebra.ι R e * d x) :
    d = contractLeft φ := sorry

end CliffordAlgebra

/-- The degree `n + 1` Koszul differential is contraction by `φ` restricted to exterior powers. -/
noncomputable def koszulDifferentialLinearMap (φ : E →ₗ[R] R) (n : ℕ) :
    ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^n E :=
  (CliffordAlgebra.contractLeft φ).restrict fun x hx ↦ contractLeft_mem_exteriorPower φ n x hx

/-- The degree `n + 1` differential of the Koszul complex of `φ`, as a morphism in `ModuleCat R`. -/
@[stacks 0622 "(2), Koszul differential"]
noncomputable abbrev koszulDifferential (φ : E →ₗ[R] R) (n : ℕ) :
    (ModuleCat.of R E).exteriorPower (n + 1) ⟶ (ModuleCat.of R E).exteriorPower n :=
  ModuleCat.ofHom (koszulDifferentialLinearMap φ n)

/-- Coercing the restricted Koszul differential to the exterior algebra recovers contraction. -/
@[simp]
theorem koszulDifferentialLinearMap_apply_coe
    (φ : E →ₗ[R] R) (n : ℕ) (x : ⋀[R]^(n + 1) E) :
    (koszulDifferentialLinearMap φ n x : ExteriorAlgebra R E) = CliffordAlgebra.contractLeft φ x := sorry

/-- On an exterior-power generator, the Koszul differential is the alternating deletion sum. -/
theorem koszulDifferentialLinearMap_apply_ιMulti_eq_sum
    (φ : E →ₗ[R] R) (n : ℕ) (v : Fin (n + 1) → E) :
    koszulDifferentialLinearMap φ n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ k : Fin (n + 1), ((-1 : R) ^ (k : ℕ) * φ (v k)) •
        exteriorPower.ιMulti R n (fun i ↦ v (Fin.succAbove k i)) := sorry

/-- Consecutive Koszul differentials compose to zero. -/
theorem koszulDifferential_sq (φ : E →ₗ[R] R) (n : ℕ) :
    koszulDifferential φ (n + 1) ≫ koszulDifferential φ n =
      (0 : (ModuleCat.of R E).exteriorPower (n + 2) ⟶ (ModuleCat.of R E).exteriorPower n) := sorry

/-- The Koszul chain complex attached to an `R`-linear form `φ : E →ₗ[R] R`. -/
@[stacks 0622 "Koszul complex of a linear form"]
noncomputable abbrev koszulComplex (φ : E →ₗ[R] R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of ((ModuleCat.of R E).exteriorPower)
    (koszulDifferential φ)
    (koszulDifferential_sq φ)

/-- Left exterior multiplication by `e` on homogeneous exterior powers. -/
@[stacks 0622 "left exterior multiplication in the Koszul complex"]
noncomputable abbrev koszulLeftWedge (e : E) (n : ℕ) :
    ⋀[R]^n E →ₗ[R] ⋀[R]^(n + 1) E :=
  exteriorPower.leftWedge e n

namespace KoszulComplex

/-- The degree `n` term of a Koszul complex is the `n`th exterior power. -/
@[simp, stacks 0622 "(1), Koszul complex term"]
theorem X (φ : E →ₗ[R] R) (n : ℕ) :
    (koszulComplex φ).X n = (ModuleCat.of R E).exteriorPower n := sorry

/-- Left exterior multiplication as a morphism between the actual terms of the Koszul complex. -/
@[stacks 0626 "left-wedge morphism on Koszul-complex terms"]
noncomputable def leftWedge (e : E) (n : ℕ) :
    (ModuleCat.of R E).exteriorPower n ⟶ (ModuleCat.of R E).exteriorPower (n + 1) :=
  ModuleCat.ofHom (koszulLeftWedge e n)

/-- The underlying linear map of the categorical left-wedge morphism. -/
@[simp]
theorem leftWedge_hom (e : E) (n : ℕ) :
    (leftWedge (R := R) e n).hom = koszulLeftWedge (R := R) e n := sorry

end KoszulComplex

/-- Left wedge sends an exterior-power generator to the generator with `e` prepended. -/
@[simp]
theorem koszulLeftWedge_apply_ιMulti (e : E) (n : ℕ) (x : Fin n → E) :
    koszulLeftWedge e n (exteriorPower.ιMulti R n x) =
      exteriorPower.ιMulti R (n + 1) (Matrix.vecCons e x) := sorry

/-- Coercing a left wedge to the exterior algebra is multiplication by the degree-one generator. -/
@[simp]
theorem koszulLeftWedge_apply_coe (e : E) (n : ℕ) (x : ⋀[R]^n E) :
    (koszulLeftWedge e n x : ExteriorAlgebra R E) = ι R e * x := sorry

namespace KoszulDifferential

/-- In degree one, contraction followed by the scalar exterior-power equivalence is the original
linear form. -/
@[stacks 0622 "(2), degree-one Koszul differential"]
theorem zero_oneEquiv (φ : E →ₗ[R] R) (v : E) :
    (exteriorPower.zeroEquiv R E)
        (koszulDifferentialLinearMap φ 0 ((exteriorPower.oneEquiv R E).symm v)) = φ v := sorry

/-- In degree zero, contraction after left wedge is multiplication by `φ e`. -/
@[stacks 0626 "degree-zero contraction-wedge relation"]
theorem comp_leftWedge_zero
    (φ : E →ₗ[R] R) (e : E) :
    (koszulDifferentialLinearMap φ 0).comp (koszulLeftWedge e 0) =
      (φ e) • (LinearMap.id : ⋀[R]^0 E →ₗ[R] ⋀[R]^0 E) := sorry

/-- Contraction and left wedge satisfy the standard Koszul homotopy relation in positive degree. -/
@[stacks 0626 "contraction-wedge homotopy relation"]
theorem comp_leftWedge_add_comp
    (φ : E →ₗ[R] R) (e : E) (n : ℕ) :
    (koszulDifferentialLinearMap φ (n + 1)).comp (koszulLeftWedge e (n + 1)) +
        (koszulLeftWedge e n).comp (koszulDifferentialLinearMap φ n) =
      (φ e) • (LinearMap.id : ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^(n + 1) E) := sorry

end KoszulDifferential

/-- The linear form on `E × R` given by `φ` on `E` and multiplication by `a` on `R`. -/
@[stacks 0622 "linear form after adjoining one Koszul element"]
noncomputable abbrev koszulCoprodScalarLinearMap (φ : E →ₗ[R] R) (a : R) :
    E × R →ₗ[R] R :=
  φ.coprod ((LinearMap.id : R →ₗ[R] R).smulRight a)

/-- Evaluate the coproduct linear form defining an appended scalar Koszul factor. -/
@[simp]
theorem koszulCoprodScalarLinearMap_apply
    (φ : E →ₗ[R] R) (a : R) (x : E × R) :
    koszulCoprodScalarLinearMap φ a x = φ x.1 + x.2 * a := sorry
