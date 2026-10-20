/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Sequence.Regularity.Append

/-!
# Permutable regular sequences

This leaf relates permutation-invariant regularity of a finite list to its
ordered sublists and to the coordinate sequence in a multivariable polynomial
ring.  The module-valued permutation criterion is kept separate from the
self-module polynomial comparison.

@stack 07DW
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence.IsRegular

variable {R : Type u} [CommRing R]

/-- A finite sequence is regular in every ordering exactly when every ordered
sublist is regular.  This module-valued criterion does not require a
properness hypothesis. -/
theorem perm_iff_sublist {M : Type v} [AddCommGroup M] [Module R M]
    (fs : List R) :
    (∀ gs : List R, List.Perm gs fs → IsRegular M gs) ↔
      ∀ gs : List R, List.Sublist gs fs → IsRegular M gs := sorry

/-- For a list generating a proper ideal, regularity of every ordered sublist
is equivalent to regularity of its coordinate sequence in the polynomial ring
with one variable for each list entry. -/
theorem sublist_iff_mvPolynomial {fs : List R} (hproper : Ideal.ofList fs ≠ ⊤) :
    (∀ gs : List R, List.Sublist gs fs → IsRegular R gs) ↔
      IsRegular (MvPolynomial (Fin fs.length) R)
        (List.ofFn fun i : Fin fs.length ↦ MvPolynomial.C (fs[i]) * MvPolynomial.X i) := sorry

/-- Lemma 10.68.10 (Stacks tag `07DW`): for a list generating a proper ideal,
permutation-invariant regularity, regularity of all ordered sublists, and
regularity of the polynomial coordinate sequence are equivalent. -/
@[stacks 07DW "permutable regular sequences and polynomial variables"]
theorem perm_sublist_mvPolynomial_tfae {fs : List R} (hproper : Ideal.ofList fs ≠ ⊤) :
    List.TFAE
      [ (∀ gs : List R, List.Perm gs fs → IsRegular R gs),
        (∀ gs : List R, List.Sublist gs fs → IsRegular R gs),
        IsRegular (MvPolynomial (Fin fs.length) R)
          (List.ofFn fun i : Fin fs.length ↦ MvPolynomial.C (fs[i]) * MvPolynomial.X i) ] := sorry

end RingTheory.Sequence.IsRegular
