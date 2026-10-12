/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

universe u v w

/-- A linear map into an injective module is an injective hull when it is injective and
its range has nonzero intersection with every nonzero submodule of the target. -/
structure LinearMap.IsInjectiveHull
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    {I : Type w} [AddCommGroup I] [Module R I] [Module.Injective R I]
    (f : M →ₗ[R] I) : Prop where
  injective : Function.Injective f
  essential : ∀ P : Submodule R I, P ≠ ⊥ → f.range ⊓ P ≠ ⊥

namespace LinearMap.IsInjectiveHull

/-- Construct an injective hull from injectivity and the essential-range criterion. -/
def of {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    {I : Type w} [AddCommGroup I] [Module R I] [Module.Injective R I]
    {f : M →ₗ[R] I} (injective : Function.Injective f)
    (essential : ∀ P : Submodule R I, P ≠ ⊥ → f.range ⊓ P ≠ ⊥) :
    f.IsInjectiveHull := LinearMap.IsInjectiveHull.mk (f := f) injective essential

/-- An injective hull is equivalently an injective map whose range meets every nonzero
submodule of its injective target nontrivially. -/
theorem iff_injective_and_essential
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    {I : Type w} [AddCommGroup I] [Module R I] [Module.Injective R I]
    {f : M →ₗ[R] I} :
    f.IsInjectiveHull ↔
      Function.Injective f ∧
        ∀ P : Submodule R I, P ≠ ⊥ → f.range ⊓ P ≠ ⊥ := sorry

/-- A linear map between modules extends to a linear map between their injective hulls,
compatibly with the hull embeddings. -/
theorem exists_lift
    {R : Type u} [Ring R]
    {M N E E' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E] [AddCommGroup E']
    [Module R M] [Module R N] [Module R E] [Module R E']
    [Module.Injective R E] [Module.Injective R E']
    {i : M →ₗ[R] E} {j : N →ₗ[R] E'} (hi : i.IsInjectiveHull)
    (hj : j.IsInjectiveHull) (φ : M →ₗ[R] N) :
    ∃ ψ : E →ₗ[R] E', ψ.comp i = j.comp φ := sorry

/-- An injective linear map between modules extends injectively between their injective hulls. -/
theorem exists_injective_lift
    {R : Type u} [Ring R]
    {M N E E' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E] [AddCommGroup E']
    [Module R M] [Module R N] [Module R E] [Module R E']
    [Module.Injective R E] [Module.Injective R E']
    {i : M →ₗ[R] E} {j : N →ₗ[R] E'} (hi : i.IsInjectiveHull)
    (hj : j.IsInjectiveHull) {φ : M →ₗ[R] N} (hφ : Function.Injective φ) :
    ∃ ψ : E →ₗ[R] E', ψ.comp i = j.comp φ ∧ Function.Injective ψ := sorry

/-- An essential injective linear map between modules extends to a linear equivalence between
their injective hulls. -/
theorem exists_linearEquiv_of_essential
    {R : Type u} [Ring R]
    {M N E E' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E] [AddCommGroup E']
    [Module R M] [Module R N] [Module R E] [Module R E']
    [Module.Injective R E] [Module.Injective R E']
    {i : M →ₗ[R] E} {j : N →ₗ[R] E'} (hi : i.IsInjectiveHull)
    (hj : j.IsInjectiveHull) {φ : M →ₗ[R] N} (hφ : Function.Injective φ)
    (hφessential : ∀ P : Submodule R N, P ≠ ⊥ → φ.range ⊓ P ≠ ⊥) :
    ∃ e : E ≃ₗ[R] E', e.toLinearMap.comp i = j.comp φ := sorry

/-- A bijective linear map between modules extends to a compatible linear equivalence between
their injective hulls. -/
theorem exists_linearEquiv_of_bijective
    {R : Type u} [Ring R]
    {M N E E' : Type v}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E] [AddCommGroup E']
    [Module R M] [Module R N] [Module R E] [Module R E']
    [Module.Injective R E] [Module.Injective R E']
    {i : M →ₗ[R] E} {j : N →ₗ[R] E'} (hi : i.IsInjectiveHull)
    (hj : j.IsInjectiveHull) {φ : M →ₗ[R] N} (hφ : Function.Bijective φ) :
    ∃ e : E ≃ₗ[R] E', e.toLinearMap.comp i = j.comp φ := sorry

/-- An embedding of a module into an injective module splits as its injective hull and a
complementary module, compatibly with the two embeddings. -/
theorem exists_complement
    {R : Type u} [Ring R]
    {M E I : Type v}
    [AddCommGroup M] [AddCommGroup E] [AddCommGroup I]
    [Module R M] [Module R E] [Module R I]
    [Module.Injective R E] [Module.Injective R I]
    {i : M →ₗ[R] E} (hi : i.IsInjectiveHull) {k : M →ₗ[R] I}
    (hk : Function.Injective k) :
    ∃ (I' : Type v) (_ : AddCommGroup I') (_ : Module R I') (e : I ≃ₗ[R] E × I'),
      e.toLinearMap.comp k = (LinearMap.inl R E I').comp i := sorry

/-- Any two injective hulls of a module are linearly equivalent by an equivalence compatible
with their hull embeddings. -/
theorem exists_linearEquiv
    {R : Type u} [Ring R]
    {M E E' : Type v}
    [AddCommGroup M] [AddCommGroup E] [AddCommGroup E']
    [Module R M] [Module R E] [Module R E']
    [Module.Injective R E] [Module.Injective R E']
    {i : M →ₗ[R] E} {j : M →ₗ[R] E'} (hi : i.IsInjectiveHull)
    (hj : j.IsInjectiveHull) :
    ∃ e : E ≃ₗ[R] E', e.toLinearMap.comp i = j := sorry

end LinearMap.IsInjectiveHull
