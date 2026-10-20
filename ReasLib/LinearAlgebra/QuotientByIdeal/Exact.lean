/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import ReasLib.LinearAlgebra.QuotientByIdeal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness after quotienting by an ideal

This leaf owns the reusable exactness transport for the canonical
`LinearMap.quotientMapByIdeal` construction.  The source-facing hypotheses
are only exactness upstairs and surjectivity of the right-hand map; no chapter
specific completion or Hilbert--Samuel data is involved.
-/

@[expose] public section

universe u v w x

namespace Function.Exact

variable {R : Type u} [Ring R]

/-- An exact pair of linear maps remains exact after quotienting all three
modules by the same ideal, provided the right-hand map is surjective. -/
theorem quotientMapByIdeal_of_surjective
    {P : Type v} {Q : Type w} {T : Type x}
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T]
    {f : P →ₗ[R] Q} {g : Q →ₗ[R] T}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (I : Ideal R) :
    Function.Exact (f.quotientMapByIdeal I) (g.quotientMapByIdeal I) := sorry

/-- Tag `087P`: if both induced quotient maps are injective, exactness forces the
left module quotient by the ideal to be subsingleton. -/
@[stacks 087P "exact quotient injectivity kills the left quotient"]
theorem quotient_subsingleton_of_injective
    {P : Type v} {Q : Type w} {T : Type x}
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T]
    (I : Ideal R) (φ : P →ₗ[R] Q) (ψ : Q →ₗ[R] T)
    (hφq : Function.Injective (φ.quotientMapByIdeal I))
    (hψq : Function.Injective (ψ.quotientMapByIdeal I))
    (hExact : Function.Exact φ ψ) :
    Subsingleton (P ⧸ (I • (⊤ : Submodule R P))) := sorry

end Function.Exact
