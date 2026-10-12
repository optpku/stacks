/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.LocallyFree

@[expose] public section

/-!
# Cotangent Summands and Finite Projective Dimension

This leaf lifts complemented finite-free summands of `I / I²` to regular sequences in `I` when
the ideal has finite projective dimension over a Noetherian local ring.
-/

open CategoryTheory

universe u

namespace Ideal.Cotangent

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {I : Ideal R}

/-- Lemma 23.11.1 (Tag 0FJQ): a complemented rank-one summand of `I / I²` lifts to a
nonzerodivisor in `I` which generates that summand. -/
@[stacks 0FJQ]
theorem exists_nonzerodivisor_lifting
    {F : Submodule (R ⧸ I) I.Cotangent}
    (hpd : projectiveDimension (ModuleCat.of R I) ≠ ⊤)
    (hFcompl : IsComplemented F)
    (hF : Nonempty (F ≃ₗ[R ⧸ I] (R ⧸ I))) :
    ∃ x : I,
      (x : R) ∈ nonZeroDivisors R ∧
        Submodule.span (R ⧸ I) {I.toCotangent x} = F := sorry

/-- A complemented cotangent summand which is finite locally free of rank `r` lifts to a regular
sequence of length `r` whose cotangent classes generate the summand. -/
theorem exists_regularSequence_lifting_of_rank
    {r : ℕ} {F : Submodule (R ⧸ I) I.Cotangent}
    (hpd : projectiveDimension (ModuleCat.of R I) ≠ ⊤)
    (hFcompl : IsComplemented F)
    [Module.FiniteLocallyFreeOfRank (R ⧸ I) F r] :
    ∃ x : Fin r → I,
      RingTheory.Sequence.IsRegular R (List.ofFn fun i ↦ (x i : R)) ∧
        Submodule.span (R ⧸ I) (Set.range fun i ↦ I.toCotangent (x i)) = F := sorry

/-- Lemma 23.11.2 (Tag 0FJR): a complemented cotangent summand explicitly identified with a
free module of rank `r` lifts to a regular sequence whose cotangent classes generate it. -/
@[stacks 0FJR]
theorem exists_regularSequence_lifting
    {r : ℕ} {F : Submodule (R ⧸ I) I.Cotangent}
    (hpd : projectiveDimension (ModuleCat.of R I) ≠ ⊤)
    (hFcompl : IsComplemented F)
    (hF : Nonempty (F ≃ₗ[R ⧸ I] (Fin r → R ⧸ I))) :
    ∃ x : Fin r → I,
      RingTheory.Sequence.IsRegular R (List.ofFn fun i ↦ (x i : R)) ∧
        Submodule.span (R ⧸ I) (Set.range fun i ↦ I.toCotangent (x i)) = F := sorry

end Ideal.Cotangent
