module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import ReasLib.RingTheory.Ideal.Tensor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Basis lifting across nilpotent quotients

This leaf owns the universe-polymorphic basis-lifting criterion in terms of injectivity of ideal
tensor multiplication.  The same-universe first-`Tor` formulation is retained as a source-facing
bridge.  The source family and its chosen quotient basis stay explicit.
-/

@[expose] public section

universe u v w

namespace Module.Basis.Nilpotent

variable {R : Type u} [CommRing R]
variable {A : Type w}

section Tensor

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Stacks `051H`, ideal-tensor form: a family whose image is a basis modulo a nilpotent ideal is
a basis upstairs when multiplication `I ⊗[R] M → M` is injective.  This is the canonical
universe-polymorphic owner of the lifting criterion. -/
@[stacks 051H "ideal tensor form"]
theorem of_quotient_basis
    (I : Ideal R) (x : A → M)
    (hI : IsNilpotent I)
    (bbar : Module.Basis A (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hbasis : ∀ a, bbar a = Submodule.mkQ (I • (⊤ : Submodule R M)) (x a))
    (hinj : Function.Injective (I.tensorMul M)) :
    ∃ b : Module.Basis A R M, ∀ a, b a = x a := sorry

end Tensor

section Tor

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Lemma 10.101.3 (Stacks `051H`): a family whose image is a basis modulo a nilpotent ideal is
a basis upstairs when the quotient-first degree-one `Tor` obstruction vanishes. -/
@[stacks 051H]
theorem of_quotient_basis_of_tor_one
    (I : Ideal R) (x : A → M)
    (hI : IsNilpotent I)
    (bbar : Module.Basis A (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hbasis : ∀ a, bbar a = Submodule.mkQ (I • (⊤ : Submodule R M)) (x a))
    (htor : IsZero (Tor₁[R](R ⧸ I, M))) :
    ∃ b : Module.Basis A R M, ∀ a, b a = x a := sorry

end Tor

end Module.Basis.Nilpotent
