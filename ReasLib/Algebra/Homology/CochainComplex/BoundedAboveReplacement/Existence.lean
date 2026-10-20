/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Comparison
public import ReasLib.CategoryTheory.ObjectProperty.Cover
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of Bounded-Above Replacements

This file states both the source-facing existence results and their canonical left-resolution
forms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex.Minus.TermsIn

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.HasEpiCover]

/-- Stacks 05T7 (1): a cochain complex that is zero above `a` admits a
termwise-epimorphic quasi-isomorphic replacement by a complex that is zero
above `a` and whose terms satisfy `P`. -/
@[stacks 05T7]
theorem exists_epiQuasiIso_of_bound
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      Bounded.QuasiIso.Epi P a K Q α := sorry

/-- Stacks 05T7 (2): if the homology of a cochain complex vanishes above
`a`, it admits a quasi-isomorphic replacement that is zero above `a` and
whose terms satisfy `P`. -/
@[stacks 05T7]
theorem exists_quasiIso_of_homology
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      Bounded.QuasiIso P a K Q α := sorry

namespace Resolution

/-- The bounded-above replacement theorem, exposed directly as a canonical epimorphic left
resolution. -/
@[stacks 05T7 "canonical epimorphic bounded-above replacement"]
theorem nonempty_epi_of_bound
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    Nonempty (CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom.Epi P a K) := sorry

/-- The homology-vanishing replacement theorem, exposed directly as a canonical left
resolution. -/
@[stacks 05T7 "canonical bounded-above replacement from homology vanishing"]
theorem nonempty_of_homology
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    Nonempty (CochainComplex.StrictlyLE.TermsIn.QuasiIsoFrom P a K) := sorry

end Resolution

end CochainComplex.Minus.TermsIn

