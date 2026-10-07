module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap64.Lemma_64_20_6_Homology
public import stacks_project.Chap64.Lemma_64_20_6_Trace
public import stacks_project.Chap64.Lemma_64_20_6_ZModPow

/-!
# Assembling traces of a Cartesian system of perfect complexes

An algebra lemma assembling traces of compatible perfect derived endomorphisms
over `ZMod (ℓ ^ (n + 1))` to a `ℤ_[ℓ]`-class, with finite inverse-limit
homology and a cohomological trace identity in `ℚ_[ℓ]`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open DerivedCategory.IsPerfect

namespace DerivedCategory.IsPerfect

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable (K : (n : ℕ) → DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))))
variable (hK : ∀ n, (K n).IsPerfect)
variable (π : ∀ n, End (K n))
variable (φ : ∀ n, (derivedBaseChange ℓ n).obj (K (n + 1)) ≅ K n)
variable (hπ : ∀ n,
    CommSq ((derivedBaseChange ℓ n).map (π (n + 1))) (φ n).hom (φ n).hom (π n))

include K hK π φ hπ

/-- Lemma 64.20.6 (1). The stage traces `t_n = Tr(π_n | K_n)` in `ZMod (ℓ ^ (n + 1))`
assemble uniquely to an element `t_∞` of `ℤ_[ℓ]`. Source `K_n` over `ZMod (ℓ ^ n)` is
Lean stage `n - 1` with coefficients `ZMod (ℓ ^ (n + 1))`. -/
@[stacks 03V4]
theorem existsUnique_tracePadic :
    ∃! t : ℤ_[ℓ], ∀ n, PadicInt.toZModPow (n + 1) t = stageTrace K hK π n := sorry

/-- Lemma 64.20.6 (2). Inverse-limit homology `H_∞^i = lim H^i(K_n)` is a finite
`ℤ_[ℓ]`-module. -/
@[stacks 03V4]
theorem moduleFinite_homologyLimit (i : ℤ) :
    Module.Finite ℤ_[ℓ] (homologyLimit K φ i) := sorry

/-- Lemma 64.20.6 (3). Inverse-limit homology `H_∞^i` is the zero module for all but
finitely many cohomological degrees `i : ℤ`. -/
@[stacks 03V4]
theorem finiteSupport_homologyLimit :
    {i : ℤ | ¬ IsZero (homologyLimit K φ i)}.Finite := sorry

/-- Lemma 64.20.6 (4). The operators `H^i(π_n)` are compatible and induce
`π_∞^i : H_∞^i ⟶ H_∞^i` satisfying
`∑ᶠ_i (-1)^i Tr(π_∞^i | H_∞^i ⊗[ℤ_[ℓ]] ℚ_[ℓ]) = t_∞` in `ℚ_[ℓ]`. -/
@[stacks 03V4]
theorem trace_eq_sum_homologyLimitEnd (t : ℤ_[ℓ])
    (ht : ∀ n, PadicInt.toZModPow (n + 1) t = stageTrace K hK π n) :
    (∑ᶠ i : ℤ, (-1 : ℚ_[ℓ]) ^ i *
        LinearMap.trace ℚ_[ℓ] _ (homologyLimitEndQEll K π φ hπ i)) =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] t := sorry

end DerivedCategory.IsPerfect
