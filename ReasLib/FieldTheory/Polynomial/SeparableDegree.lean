module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open Polynomial

universe u v

namespace Polynomial

variable {F : Type u} [Field F]
variable {Ω : Type v} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]

/-- Definition 9.12.6 (Tag 09H5): over an algebraically closed extension, the separable degree
of a polynomial is the number of its distinct roots. -/
theorem natSepDegree_eq_card_rootSet (P : F[X]) :
    P.natSepDegree = Fintype.card (P.rootSet Ω) := by
  classical
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe] using
    (natSepDegree_eq_of_isAlgClosed Ω P)

/-- Lemma 9.12.4 (Tag 09H3): an irreducible polynomial is separable exactly when the roots of
its image in an algebraic closure have no repetitions. -/
theorem irreducibleSeparableIffNodupRootsMapAlgebraicClosure {P : F[X]} (hP : Irreducible P) :
    P.Separable ↔ ((P.map (algebraMap F (AlgebraicClosure F))).roots).Nodup := by
  rw [← separable_map (algebraMap F (AlgebraicClosure F)),
    ← nodup_roots_iff_of_splits (Polynomial.map_ne_zero hP.ne_zero) (IsAlgClosed.splits _)]

variable {p : ℕ} [Fact p.Prime] [CharP F p]

/-- Lemma 9.12.5 (Tag 09H4): over an algebraically closed extension of a characteristic-`p`
field, `P` and `P.comp (X ^ p)` have the same number of distinct roots. -/
theorem card_rootSet_comp_X_pow_eq (P : F[X]) :
    Fintype.card ((P.comp (X ^ p)).rootSet Ω) = Fintype.card (P.rootSet Ω) := by
  rw [← natSepDegree_eq_card_rootSet (Ω := Ω) (P.comp (X ^ p)),
    ← natSepDegree_eq_card_rootSet (Ω := Ω) P]
  simpa [pow_one, expand_eq_comp_X_pow] using
    (natSepDegree_expand P p : (expand F (p ^ 1) P).natSepDegree = P.natSepDegree)

end Polynomial
