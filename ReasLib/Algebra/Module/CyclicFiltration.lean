/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Order.RelSeries
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cyclic filtrations of modules

This file owns the generic submodule relation whose successive quotient is a
quotient of the base ring, together with the finite cyclic filtration theorem.
The relation is deliberately broader than the prime-quotient relation used by
prime filtrations.
-/

@[expose] public section

universe u v

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Two submodules form a cyclic quotient step when the larger contains the
smaller and their quotient is linearly equivalent to `R ⧸ I` for some ideal
`I`. -/
@[stacks 00KZ "cyclic quotient submodule step"]
def IsQuotientEquivQuotient (N₁ N₂ : Submodule R M) : Prop :=
  N₁ ≤ N₂ ∧
    ∃ I : Ideal R,
      Nonempty ((N₂ ⧸ N₁.submoduleOf N₂) ≃ₗ[R] R ⧸ I)

/-- Adjoining one element to a submodule gives a cyclic quotient step. -/
@[stacks 00KZ "adjoining one element gives a cyclic quotient"]
theorem isQuotientEquivQuotient_sup_span (N : Submodule R M) (x : M) :
    IsQuotientEquivQuotient N (N ⊔ span R ({x} : Set M)) := sorry
/- Proof strategy: identify the quotient by `N` with the cyclic span of the
class of `x`, then identify that cyclic module with `R ⧸ Ideal.torsionOf`. -/

end Submodule

namespace Module

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- A cyclic filtration is a relation series of submodules whose successive
quotients are cyclic quotients of the base ring. -/
@[stacks 00KZ "cyclic filtration"]
abbrev CyclicFiltration :=
  RelSeries {(N₁, N₂) : Submodule R M × Submodule R M |
    Submodule.IsQuotientEquivQuotient N₁ N₂}

namespace CyclicFiltration

/-- The `i`th successive quotient of a cyclic filtration. -/
abbrev successiveQuotient (s : CyclicFiltration R M) (i : Fin s.length) :=
  (s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)

end CyclicFiltration

end Module

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Lemma 10.5.4 (Tag 00KZ): every finite module has a finite cyclic
filtration from `⊥` to `⊤`. -/
@[stacks 00KZ "finite cyclic filtration of a finite module"]
theorem exists_finite_cyclic_filtration :
    ∃ s : CyclicFiltration R M, s.head = ⊥ ∧ s.last = ⊤ := sorry
/- Proof strategy: choose a finite generating family and append one
`isQuotientEquivQuotient_sup_span` step for each generator. -/

end Module
