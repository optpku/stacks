module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.LinearMap.SemilinearPi

/-!
# Finite-coordinate semilinear maps after restricting scalars

This leaf packages a target transported along a ring homomorphism as the canonical
`ModuleCat.restrictScalars` object.  It keeps the selected scalar action in the codomain type,
so public map statements do not expose a proof-local `Module.compHom` instance.
-/

@[expose] public section

universe u v w t

namespace LinearMap.RestrictScalars

variable {R : Type u} {S : Type v} {T : Type t} {M : Type w} {ι : Type*}
variable [Semiring R] [CommRing S] [CommRing T]
variable [AddCommGroup M] [Module T M]

/-- Extend a finite-coordinate semilinear map after restriction of scalars along `φ`.  The
codomain is the canonical `ModuleCat.restrictScalars φ` object, so the transported `S`-module
structure is part of the type and does not leak as a consumer-visible local instance. -/
@[stacks 052N "semilinear finite free scalar transport"]
noncomputable def extendPi
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* T) (φ : S →+* T) (τ : (ι → R) →ₛₗ[σ] M) :
    (ι → S) →ₗ[S] ((ModuleCat.restrictScalars φ).obj (ModuleCat.of T M)) :=
  (Pi.basisFun S ι).constr S (fun i ↦ τ (Pi.single i 1))

/-- Evaluation of `LinearMap.RestrictScalars.extendPi` by the transported standard-basis sum. -/
@[simp, stacks 052N "semilinear finite free scalar transport evaluation"]
theorem extendPi_apply
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* T) (φ : S →+* T) (τ : (ι → R) →ₛₗ[σ] M)
    (x : ι → S) :
    extendPi σ φ τ x = ∑ i, φ (x i) • τ (Pi.single i 1) := sorry

/-- The bundled scalar-transport extension is surjective when both the scalar map and the
original semilinear presentation are surjective. -/
@[stacks 052N "semilinear finite free scalar transport surjective"]
theorem extendPi_surjective
    [Fintype ι] [DecidableEq ι]
    (σ : R →+* T) (φ : S →+* T) (τ : (ι → R) →ₛₗ[σ] M)
    (hφ : Function.Surjective φ) (hτ : Function.Surjective τ) :
    Function.Surjective (extendPi σ φ τ) := sorry

end LinearMap.RestrictScalars
