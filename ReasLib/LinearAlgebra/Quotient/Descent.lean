module

public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Descent along surjective linear maps

This leaf packages the universal factorization of a linear map through a
surjective linear map when it kills the latter's kernel.

@stack 07HY
-/

@[expose] public section

noncomputable section

universe u v w x

namespace LinearMap

variable {R : Type u} [Ring R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {W : Type w} [AddCommGroup W] [Module R W]
variable {X : Type x} [AddCommGroup X] [Module R X]

/-- The linear map induced on the codomain of a surjective map by a map that kills its kernel. -/
@[stacks 07HY]
noncomputable def descendOfSurjective
    (q : V →ₗ[R] W) (hq : Function.Surjective q)
    (f : V →ₗ[R] X) (hker : LinearMap.ker q ≤ LinearMap.ker f) :
    W →ₗ[R] X :=
  ((LinearMap.ker q).liftQ f hker).comp
    (q.quotKerEquivOfSurjective hq).symm.toLinearMap

/-- `descendOfSurjective` factors its input map through the given surjection. -/
@[simp, stacks 07HY "linear descent factorization"]
theorem descendOfSurjective_comp
    (q : V →ₗ[R] W) (hq : Function.Surjective q)
    (f : V →ₗ[R] X) (hker : LinearMap.ker q ≤ LinearMap.ker f) :
    (descendOfSurjective q hq f hker).comp q = f := by
  ext x
  simp [descendOfSurjective]

/-- `descendOfSurjective` sends the image of a representative to the image of that representative. -/
@[simp, stacks 07HY "linear descent evaluation"]
theorem descendOfSurjective_apply
    (q : V →ₗ[R] W) (hq : Function.Surjective q)
    (f : V →ₗ[R] X) (hker : LinearMap.ker q ≤ LinearMap.ker f)
    (x : V) :
    descendOfSurjective q hq f hker (q x) = f x := by
  exact LinearMap.congr_fun (descendOfSurjective_comp q hq f hker) x

/-- A linear map out of the codomain of a surjection is determined by its composite with that
surjection. -/
@[stacks 07HY "linear descent uniqueness"]
theorem eq_descendOfSurjective_of_comp_eq
    (q : V →ₗ[R] W) (hq : Function.Surjective q)
    (f : V →ₗ[R] X) (hker : LinearMap.ker q ≤ LinearMap.ker f)
    (g : W →ₗ[R] X) (hg : g.comp q = f) :
    g = descendOfSurjective q hq f hker := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hq x
  rw [descendOfSurjective_apply]
  exact LinearMap.congr_fun hg y

end LinearMap
