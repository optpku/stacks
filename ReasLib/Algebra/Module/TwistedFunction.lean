module

public import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functions with a twisted scalar action

For a monoid acting on a semiring, this file equips `G → M` with the scalar action
`(r • f) σ = (σ • r) • f σ`.  The dependent coefficient type lets the construction reuse
mathlib's restriction-of-scalars and Pi-module instances, so the algebraic data do not depend on
deferred proofs.
-/

@[expose] public section

universe u v w

variable {G : Type u} {R : Type v} {M : Type w}
variable [Monoid G] [Semiring R] [MulSemiringAction G R]
variable [AddCommMonoid M] [Module R M]

/-- The coefficient module at `σ`; its scalars are restricted along the endomorphism of `R`
defined by `σ`. -/
def TwistedFunction.Coeff (G : Type u) (R : Type v) (M : Type w)
    [Monoid G] [Semiring R] [MulSemiringAction G R]
    [AddCommMonoid M] [Module R M] (_ : G) : Type w :=
  M

namespace TwistedFunction

/-- The additive structure on a twisted coefficient is the original additive structure. -/
instance (σ : G) : AddCommMonoid (Coeff G R M σ) :=
  inferInstanceAs (AddCommMonoid M)

/-- At `σ`, scalars act through the semiring endomorphism induced by `σ`. -/
instance (σ : G) : Module R (Coeff G R M σ) :=
  Module.compHom M (MulSemiringAction.toRingHom G R σ)

end TwistedFunction

/-- Example 18.37.3 (05V9) (1): the module of functions `G → M` with twisted scalar action
`(r • f) σ = (σ • r) • f σ`. -/
@[stacks 05V9 "(1)"]
def TwistedFunction (G : Type u) (R : Type v) (M : Type w)
    [Monoid G] [Semiring R] [MulSemiringAction G R]
    [AddCommMonoid M] [Module R M] : Type (max u w) :=
  (σ : G) → TwistedFunction.Coeff G R M σ

namespace TwistedFunction

/-- The pointwise additive structure on twisted functions. -/
instance : AddCommMonoid (TwistedFunction G R M) :=
  inferInstanceAs (AddCommMonoid ((σ : G) → Coeff G R M σ))

/-- The module structure on twisted functions obtained from the restricted scalar action in every
coordinate. -/
instance : Module R (TwistedFunction G R M) :=
  inferInstanceAs (Module R ((σ : G) → Coeff G R M σ))

/-- The additive constant-function map into the twisted function module. -/
def const : M →+ TwistedFunction G R M :=
  Pi.constAddMonoidHom G M

/-- Evaluation of a twisted function at the identity is linear.  The codomain is displayed as
the restricted coefficient module at `1`; its underlying type is definitionally `M`. -/
def evalOne : TwistedFunction G R M →ₗ[R] Coeff G R M 1 :=
  LinearMap.proj (R := R) (φ := fun σ : G => Coeff G R M σ) (1 : G)

/-- Example 18.37.3 (05V9) (2): the augmentation submodule consists of twisted functions that
vanish at the identity. -/
@[stacks 05V9 "(2)"]
def augmentation : Submodule R (TwistedFunction G R M) :=
  LinearMap.ker (evalOne (G := G) (R := R) (M := M))

/-- Evaluation of the additive constant-function map returns its input. -/
@[simp]
theorem const_apply (m : M) (σ : G) :
    const (G := G) (R := R) (M := M) m σ = m := sorry

/-- The scalar action on twisted functions is given by the action of the coordinate on the
scalar. -/
@[simp]
theorem smul_apply (r : R) (f : TwistedFunction G R M) (σ : G) :
    (r • f) σ = (σ • r) • f σ := sorry

/-- Evaluation at the identity is ordinary evaluation. -/
@[simp]
theorem evalOne_apply (f : TwistedFunction G R M) :
    evalOne (G := G) (R := R) (M := M) f = f 1 := sorry

/-- Example 18.37.3 (05V9) (3): membership in the augmentation submodule is vanishing at the
identity. -/
@[stacks 05V9 "(3)"]
theorem mem_augmentation_iff (f : TwistedFunction G R M) :
    f ∈ augmentation (G := G) (R := R) (M := M) ↔ f 1 = 0 := sorry

section Group

variable {G' : Type u} {R' : Type v}
variable [Group G'] [Semiring R'] [MulSemiringAction G' R']

/-- Lemma 18.37.2 (05V8) (3): if the action on the coefficient semiring is nontrivial, the
additive constant-function map into `TwistedFunction G R R` is not induced by an `R`-linear
map. -/
@[stacks 05V8 "(3)"]
theorem not_exists_linearMap_eq_const
    (h : ∃ σ : G', ∃ r : R', σ • r ≠ r) :
    ¬ ∃ s : R' →ₗ[R'] TwistedFunction G' R' R',
        ∀ r : R', s r = const (G := G') (R := R') (M := R') r := sorry

end Group

end TwistedFunction
