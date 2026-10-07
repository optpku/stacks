module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

/-!
# Exact sequences over division rings

Every short exact sequence of modules over a division ring admits a compatible product
decomposition.
-/

universe u v w z

open LinearMap

namespace Function

variable {k : Type u} {V : Type v} {W : Type w} {X : Type z}
variable [DivisionRing k] [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
variable [Module k V] [Module k W] [Module k X]

/-- A short exact sequence of modules over a division ring splits as a compatible product
decomposition. -/
theorem Exact.existsLinearEquivProdOfDivisionRing
    {f : V →ₗ[k] W} {g : W →ₗ[k] X}
    (hfg : Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    ∃ e : W ≃ₗ[k] V × X, f = e.symm ∘ₗ inl k V X ∧ g = snd k V X ∘ₗ e := by
  exact ((hfg.split_tfae hf hg).out 0 2 rfl rfl).mp <|
    Module.projective_lifting_property g (LinearMap.id : X →ₗ[k] X) hg

end Function
