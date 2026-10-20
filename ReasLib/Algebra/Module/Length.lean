module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Natural-valued length and finiteness of finite-length modules

`Module.length` takes values in `ℕ∞` because arbitrary modules may have infinite
length.  This file supplies the natural-valued specialization selected by Mathlib's
canonical Noetherian and Artinian module typeclasses, together with the bridges needed
for induction on length and for recovering `Module.Finite`.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Module

variable (R : Type u) (M : Type v)
variable [Ring R] [AddCommGroup M] [Module R M]
variable [IsNoetherian R M] [IsArtinian R M]

/-- The length of a Noetherian Artinian module, as a natural number. -/
@[stacks 0BJ6 "natural-valued finite module length"]
noncomputable def natLength : ℕ :=
  WithTop.untop (Module.length R M) Module.length_ne_top

/-- The natural-valued length coerces back to `Module.length`. -/
@[simp, norm_cast]
theorem coe_natLength :
    (Module.natLength R M : ℕ∞) = Module.length R M := sorry

/-- A finite-length module has natural-valued length zero exactly when it is trivial. -/
@[simp]
theorem natLength_eq_zero_iff :
    Module.natLength R M = 0 ↔ Subsingleton M := sorry

/-- A finite-length module has positive natural-valued length exactly when it is nontrivial. -/
theorem natLength_pos_iff :
    0 < Module.natLength R M ↔ Nontrivial M := sorry

variable {R M}
variable {N : Type w} [AddCommGroup N] [Module R N]
variable [IsNoetherian R N] [IsArtinian R N]

/-- Natural-valued length is monotone along injective linear maps. -/
theorem natLength_le_of_injective (f : N →ₗ[R] M) (hf : Function.Injective f) :
    Module.natLength R N ≤ Module.natLength R M := sorry

/-- Natural-valued length is monotone along surjective linear maps. -/
theorem natLength_le_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.natLength R N ≤ Module.natLength R M := sorry

variable {P : Type*} [AddCommGroup P] [Module R P]
variable [IsNoetherian R P] [IsArtinian R P]

/-- Natural-valued length is additive in a short exact sequence of finite-length modules. -/
theorem natLength_eq_add_of_exact
    (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    Module.natLength R M = Module.natLength R N + Module.natLength R P := sorry

/-- A proper submodule of a finite-length module has strictly smaller natural-valued length. -/
theorem _root_.Submodule.natLength_lt (N : Submodule R M) (hN : N ≠ ⊤) :
    Module.natLength R N < Module.natLength R M := sorry

section Torsion

variable (R : Type u) (M : Type v)
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [IsNoetherian R (Submodule.torsion R M)]
variable [IsArtinian R (Submodule.torsion R M)]

/-- The natural-valued length of a torsion submodule when that submodule has finite length. -/
@[stacks 0BJ6 "natural-valued torsion length"]
noncomputable def torsionNatLength : ℕ :=
  Module.natLength R (Submodule.torsion R M)

/-- Natural-valued torsion length coerces to the usual `ℕ∞`-valued module length. -/
@[simp, norm_cast]
theorem coe_torsionNatLength :
    (Module.torsionNatLength R M : ℕ∞) =
      Module.length R (Submodule.torsion R M) := sorry

/-- Natural-valued torsion length vanishes exactly when the torsion submodule is trivial. -/
@[simp]
theorem torsionNatLength_eq_zero_iff :
    Module.torsionNatLength R M = 0 ↔
      Submodule.torsion R M = (⊥ : Submodule R M) := sorry

variable [IsDomain R]

/-- A module is torsion-free exactly when its natural-valued torsion length vanishes. -/
@[simp]
theorem IsTorsionFree.iff_torsionNatLength_eq_zero :
    Module.IsTorsionFree R M ↔ Module.torsionNatLength R M = 0 := sorry

end Torsion

end Module

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finite module killed by a power of a finitely generated maximal ideal has finite length. -/
@[stacks 00J0 "finite length from annihilation by a maximal-ideal power"]
theorem isFiniteLength_of_pow_smul_top_eq_bot
    (m : Ideal R) [m.IsMaximal] [Module.Finite R M]
    (hfg : m.FG) {n : ℕ}
    (hpow : m ^ n • (⊤ : Submodule R M) = ⊥) :
    IsFiniteLength R M := sorry

end Module

namespace Module

variable {R : Type u} {M : Type v}
variable [Ring R] [AddCommGroup M] [Module R M]

/-- A module has length one exactly when it is linearly equivalent to the quotient
of its ring by a maximal left ideal. -/
@[stacks 076F]
theorem length_eq_one_iff_quot_maximal :
    Module.length R M = 1 ↔
      ∃ m : Ideal R, m.IsMaximal ∧ Nonempty (M ≃ₗ[R] R ⧸ m) := sorry

/-- If `M` has finite length, then it is finite as an `R`-module. -/
@[stacks 02LZ "finite generation from finite length"]
theorem Finite.of_isFiniteLength (h : IsFiniteLength R M) : Module.Finite R M := sorry

/-- The canonical length criterion for finite generation. -/
@[stacks 02LZ "finite generation from finite module length"]
theorem finite_of_length_ne_top
    (h : Module.length R M ≠ ⊤) : Module.Finite R M := sorry

/-- Module length strictly below `⊤` implies finite generation. -/
@[stacks 02LZ "finite generation from finite module length"]
theorem finite_of_length_lt_top
    (h : Module.length R M < ⊤) : Module.Finite R M := sorry

end Module

namespace Submodule

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- If `J ≤ N`, the length of `M ⧸ J` is the sum of the lengths of `M ⧸ N`
and the subquotient `N ⧸ J`. -/
theorem length_quotient_eq_add_quotient {J N : Submodule R M} (hJN : J ≤ N) :
    Module.length R (M ⧸ J) =
      Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := sorry

/-- Enlarging the quotient submodule can only decrease module length. -/
@[stacks 00K7 "quotient length monotonicity"]
theorem length_quotient_le_of_submodule_le {J N : Submodule R M} (hJN : J ≤ N) :
    Module.length R (M ⧸ N) ≤ Module.length R (M ⧸ J) := sorry

end Submodule
