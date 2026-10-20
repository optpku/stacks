/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Computation
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated-Graded Support under Filtered Quasi-Isomorphisms

This file isolates the support transport used by filtered truncation and replacement arguments.
The API is symmetric: a filtered quasi-isomorphism identifies homology vanishing and both
cohomological support bounds on its associated graded complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.Gr

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Lower cohomological support of the associated graded complex is equivalent to vanishing of
its homology below the cutoff. -/
@[stacks 05S5 "associated-graded cohomological support"]
theorem isGE_iff (K : FilteredComplex A) (a : ℤ) :
    K.associatedGraded.IsGE a ↔
      ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n) := sorry

/-- Upper cohomological support of the associated graded complex is equivalent to vanishing of
its homology above the cutoff. -/
@[stacks 05S5 "associated-graded cohomological support"]
theorem isLE_iff (K : FilteredComplex A) (b : ℤ) :
    K.associatedGraded.IsLE b ↔
      ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n) := sorry

namespace QuasiIso

/-- Filtered quasi-isomorphisms are closed under composition. -/
@[stacks 05S5 "filtered quasi-isomorphism composition"]
theorem comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M)
    (hf : _root_.QuasiIso (associatedGradedMap f))
    (hg : _root_.QuasiIso (associatedGradedMap g)) :
    _root_.QuasiIso (associatedGradedMap (f ≫ g)) := sorry

/-- A composite and its left factor are filtered quasi-isomorphisms exactly when the right
factor is. -/
@[stacks 05S5 "filtered quasi-isomorphism cancellation"]
theorem of_comp_left {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M)
    (hf : _root_.QuasiIso (associatedGradedMap f))
    (hfg : _root_.QuasiIso (associatedGradedMap (f ≫ g))) :
    _root_.QuasiIso (associatedGradedMap g) := sorry

/-- A composite and its right factor are filtered quasi-isomorphisms exactly when the left
factor is. -/
@[stacks 05S5 "filtered quasi-isomorphism cancellation"]
theorem of_comp_right {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M)
    (hg : _root_.QuasiIso (associatedGradedMap g))
    (hfg : _root_.QuasiIso (associatedGradedMap (f ≫ g))) :
    _root_.QuasiIso (associatedGradedMap f) := sorry

/-- A filtered quasi-isomorphism preserves and reflects vanishing of associated-graded homology
in each degree. -/
@[stacks 05S5 "filtered quasi-isomorphism support"]
theorem homology_isZero_iff {K L : FilteredComplex A} (f : K ⟶ L)
    (hf : _root_.QuasiIso (associatedGradedMap f)) (n : ℤ) :
    IsZero (K.associatedGraded.homology n) ↔ IsZero (L.associatedGraded.homology n) := sorry

/-- A filtered quasi-isomorphism preserves and reflects lower cohomological support of the
associated graded complex. -/
@[stacks 05S5 "filtered quasi-isomorphism support"]
theorem isGE_iff {K L : FilteredComplex A} (f : K ⟶ L)
    (hf : _root_.QuasiIso (associatedGradedMap f)) (a : ℤ) :
    K.associatedGraded.IsGE a ↔ L.associatedGraded.IsGE a := sorry

/-- A filtered quasi-isomorphism preserves and reflects upper cohomological support of the
associated graded complex. -/
@[stacks 05S5 "filtered quasi-isomorphism support"]
theorem isLE_iff {K L : FilteredComplex A} (f : K ⟶ L)
    (hf : _root_.QuasiIso (associatedGradedMap f)) (b : ℤ) :
    K.associatedGraded.IsLE b ↔ L.associatedGraded.IsLE b := sorry

end QuasiIso

end CategoryTheory.FilteredComplex.Gr
