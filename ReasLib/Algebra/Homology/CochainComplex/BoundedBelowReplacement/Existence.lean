/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Comparison
public import ReasLib.CategoryTheory.ObjectProperty.Cover
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of Bounded-Below Replacements

This file states both the source-facing existence results and their canonical right-resolution
forms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex.Plus.TermsIn

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.HasMonoEmbedding]

/-- Stacks 05T6 (1): a cochain complex that is zero below `a` admits a
termwise-monomorphic quasi-isomorphic replacement by a complex that is zero
below `a` and whose terms satisfy `P`. -/
@[stacks 05T6]
theorem exists_monoQuasiIso_of_bound
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyGE a) :
    ∃ (I : CochainComplex A ℤ) (α : K ⟶ I),
      Bounded.QuasiIso.Mono P a K I α := sorry

/-- Stacks 05T6 (2): if the homology of a cochain complex vanishes below
`a`, it admits a quasi-isomorphic replacement that is zero below `a` and
whose terms satisfy `P`. -/
@[stacks 05T6]
theorem exists_quasiIso_of_homology
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    ∃ (I : CochainComplex A ℤ) (α : K ⟶ I),
      Bounded.QuasiIso P a K I α := sorry

namespace Resolution

/-- The bounded-below replacement theorem, exposed directly as a canonical monomorphic right
resolution. -/
@[stacks 05T6 "canonical monomorphic bounded-below replacement"]
theorem nonempty_mono_of_bound
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyGE a) :
    Nonempty (CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Mono P a K) := sorry

/-- The homology-vanishing replacement theorem, exposed directly as a canonical right
resolution. -/
@[stacks 05T6 "canonical bounded-below replacement from homology vanishing"]
theorem nonempty_of_homology
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    Nonempty (CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo P a K) := sorry

end Resolution

end CochainComplex.Plus.TermsIn

