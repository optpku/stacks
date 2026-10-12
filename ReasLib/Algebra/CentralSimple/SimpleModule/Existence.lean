/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.Recall
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-! # Existence of simple submodules

This file establishes the existence of simple submodules over Artinian rings and
finite-dimensional algebras, together with the finite-dimensionality of simple modules.

@stack 0746
-/

universe u v w

namespace IsArtinianRing

section

variable {A : Type v} [Ring A] [IsArtinianRing A]
variable {M : Type w} [AddCommGroup M] [Module A M]

/-- Every nonzero module over an Artinian ring contains a simple submodule. -/
theorem exists_simpleSubmodule [Nontrivial M] :
    ∃ N : Submodule A M, IsSimpleModule A N := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let N : Submodule A M := A ∙ m
  have hN_ne : N ≠ ⊥ := by
    intro hN
    exact hm <| by
      simpa [N, hN] using (Submodule.mem_span_singleton_self m : m ∈ A ∙ m)
  letI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN_ne
  letI : IsArtinian A N := isArtinian_of_fg_of_artinian N (Submodule.fg_span_singleton m)
  let s : Set (Submodule A N) := {S | S ≠ ⊥}
  have hs : s.Nonempty := ⟨⊤, by simp [s]⟩
  obtain ⟨S, hS, hmin⟩ := IsArtinian.set_has_minimal s hs
  have hsimple : IsSimpleModule A S := by
    rw [isSimpleModule_iff_isAtom]
    refine (isAtom_iff_le_of_ge).2 ⟨hS, ?_⟩
    intro P hP hPS
    by_contra hSP
    have hPS_ne : P ≠ S := by
      intro hEq
      subst hEq
      exact hSP le_rfl
    exact (hmin P (by simpa [s] using hP) (lt_of_le_of_ne hPS hPS_ne)).elim
  refine ⟨S.map N.subtype, ?_⟩
  letI : IsSimpleModule A S := hsimple
  exact IsSimpleModule.congr (S.equivMapOfInjective _ N.subtype_injective).symm

end

end IsArtinianRing

namespace FiniteDimensional

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
variable {M : Type w} [AddCommGroup M] [Module A M]

/-- Every nonzero `A`-module contains a simple `A`-submodule when `A` is finite
over `k`. -/
@[stacks 0746]
theorem exists_simpleSubmodule
    (k : Type u) [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
    {M : Type w} [AddCommGroup M] [Module A M] [Nontrivial M] :
    ∃ N : Submodule A M, IsSimpleModule A N := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact IsArtinianRing.exists_simpleSubmodule

/-- If the finite `k`-algebra `A` is nonzero, then the regular left
`A`-module contains a simple submodule. -/
@[stacks 0746]
theorem exists_simpleSubmodule_regular
    (k : Type u) [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Nontrivial A] :
    ∃ N : Submodule A A, IsSimpleModule A N := by
  have h : ∃ N : Submodule A A, IsSimpleModule A N := exists_simpleSubmodule k
  exact h

end

end FiniteDimensional

namespace IsSimpleModule

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
variable {M : Type w} [AddCommGroup M] [Module A M]

/-- A simple module over a finite `k`-algebra is finite dimensional over `k`. -/
@[stacks 0746]
theorem finiteDimensional [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M] : FiniteDimensional k M := by
  letI : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  letI : Module.Finite A M :=
    Module.Finite.of_surjective (LinearMap.toSpanSingleton A M m)
      (IsSimpleModule.toSpanSingleton_surjective A hm)
  exact Module.Finite.trans A M

end

end IsSimpleModule

end
