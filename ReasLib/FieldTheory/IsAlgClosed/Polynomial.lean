module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.TFAE

@[expose] public section

/-!
# Polynomial criteria for algebraically closed fields

Equivalent formulations of algebraic closedness using irreducible polynomials, roots, and
splitting.
-/

open Polynomial

universe u

namespace IsAlgClosed

variable (F : Type u) [Field F]

/-- A field is algebraically closed iff every irreducible polynomial over it is linear. -/
theorem iffForallIrreducibleDegreeEqOne :
    IsAlgClosed F ↔ ∀ (p : F[X]) (_ : Irreducible p), p.degree = 1 := by
  refine ⟨fun _ p hp ↦ IsAlgClosed.degree_eq_one_of_irreducible F hp, fun h ↦ ?_⟩
  exact IsAlgClosed.of_exists_root F fun p _ hp ↦ exists_root_of_degree_eq_one (h p hp)

/-- A field is algebraically closed iff every nonconstant polynomial over it has a root. -/
theorem iffForallNonconstantExistsRoot :
    IsAlgClosed F ↔ ∀ (p : F[X]) (_ : p.natDegree ≠ 0), ∃ x : F, IsRoot p x := by
  refine ⟨?_, ?_⟩
  · intro _ p hp
    exact IsAlgClosed.exists_root p (degree_ne_of_natDegree_ne hp)
  · intro h
    exact IsAlgClosed.of_exists_root F fun p _ hp ↦ h p hp.natDegree_pos.ne'

/-- A field is algebraically closed iff every nonconstant polynomial over it splits. -/
theorem iffForallNonconstantSplits :
    IsAlgClosed F ↔ ∀ (p : F[X]) (_ : p.natDegree ≠ 0), p.Splits := by
  refine ⟨fun _ p _ ↦ IsAlgClosed.splits p, ?_⟩
  intro h
  refine (iffForallNonconstantExistsRoot F).2 fun p hp ↦ ?_
  exact (h p hp).exists_eval_eq_zero (degree_ne_of_natDegree_ne hp)

/-- Algebraic closedness and its standard polynomial criteria are equivalent. -/
theorem polynomialTFAE :
    List.TFAE [
      IsAlgClosed F,
      ∀ (p : F[X]) (_ : Irreducible p), p.degree = 1,
      ∀ (p : F[X]) (_ : p.natDegree ≠ 0), ∃ x : F, IsRoot p x,
      ∀ (p : F[X]) (_ : p.natDegree ≠ 0), p.Splits
    ] := by
  tfae_have 1 ↔ 2 := iffForallIrreducibleDegreeEqOne F
  tfae_have 1 ↔ 3 := iffForallNonconstantExistsRoot F
  tfae_have 1 ↔ 4 := iffForallNonconstantSplits F
  tfae_finish

end IsAlgClosed
