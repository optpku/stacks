/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v w t

namespace LinearMap

variable {R : Type u} {S : Type v} {M : Type w} {ι : Type*}
variable [Semiring R] [CommSemiring S]
variable [AddCommMonoid M] [Module S M]

/-- Extend a semilinear map on a finite free `R`-module to an `S`-linear map on the corresponding
finite free `S`-module.  The image of each standard basis vector is inherited from the
semilinear map, so no auxiliary `R`-module structure on `M` is required. -/
@[stacks 052N "semilinear finite free extension"]
noncomputable def extendPi
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* S) (τ : (ι → R) →ₛₗ[σ] M) :
    (ι → S) →ₗ[S] M :=
  (Pi.basisFun S ι).constr S (fun i ↦ τ (Pi.single i 1))

/-- Evaluation of the finite-free extension by the standard-coordinate sum. -/
@[simp, stacks 052N "semilinear finite free extension evaluation"]
theorem extendPi_apply
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* S) (τ : (ι → R) →ₛₗ[σ] M) (x : ι → S) :
    extendPi σ τ x = ∑ i, x i • τ (Pi.single i 1) := sorry

/-- The explicit finite-coordinate semilinear map with prescribed images of the standard basis.
Unlike `extendPi`, this constructor starts from the basis images directly and is useful when the
target carries only the larger scalar action. -/
@[stacks 052N "finite coordinate semilinear map"]
noncomputable def piSemilinear
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* S) (f : ι → M) :
    (ι → R) →ₛₗ[σ] M :=
  { toFun := fun x ↦ ∑ i, σ (x i) • f i
    map_add' := sorry
    map_smul' := sorry }

/-- Evaluation of the explicit finite-coordinate semilinear map. -/
@[simp, stacks 052N "finite coordinate semilinear map evaluation"]
theorem piSemilinear_apply
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* S) (f : ι → M) (x : ι → R) :
    piSemilinear σ f x = ∑ i, σ (x i) • f i := sorry

/-- The finite-free extension is surjective whenever the original semilinear map is surjective. -/
@[stacks 052N "semilinear finite free extension surjective"]
theorem extendPi_surjective
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* S) (τ : (ι → R) →ₛₗ[σ] M)
    (hτ : Function.Surjective τ) :
    Function.Surjective (extendPi σ τ) := sorry

end LinearMap

namespace LinearMap

variable {R : Type u} {S : Type v} {T : Type t} {M : Type w} {ι : Type*}
variable [Semiring R] [CommSemiring S] [CommSemiring T]
variable [AddCommMonoid M] [Module T M]

/-- Semiring-generic compatibility form of finite-coordinate scalar transport.  For ring-valued
clients, prefer `LinearMap.RestrictScalars.extendPi`, whose bundled codomain records the
restriction of scalars without exposing this local module instance in the result type. -/
@[stacks 052N "semilinear finite free scalar transport"]
noncomputable def extendPiAlong
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* T) (φ : S →+* T) (τ : (ι → R) →ₛₗ[σ] M) :
    letI : Module S M := Module.compHom M φ
    (ι → S) →ₗ[S] M := by
  letI : Module S M := Module.compHom M φ
  exact (Pi.basisFun S ι).constr S (fun i ↦ τ (Pi.single i 1))

/-- Evaluation of `extendPiAlong` by the transported standard-basis sum. -/
@[simp, stacks 052N "semilinear finite free scalar transport evaluation"]
theorem extendPiAlong_apply
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* T) (φ : S →+* T) (τ : (ι → R) →ₛₗ[σ] M)
    (x : ι → S) :
    letI : Module S M := Module.compHom M φ
    extendPiAlong σ φ τ x = ∑ i, φ (x i) • τ (Pi.single i 1) := sorry

/-- The transported extension is surjective when both the scalar map and the original semilinear
presentation are surjective. -/
@[stacks 052N "semilinear finite free scalar transport surjective"]
theorem extendPiAlong_surjective
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* T) (φ : S →+* T) (τ : (ι → R) →ₛₗ[σ] M)
    (hφ : Function.Surjective φ) (hτ : Function.Surjective τ) :
    letI : Module S M := Module.compHom M φ
    Function.Surjective (extendPiAlong σ φ τ) := sorry

end LinearMap
