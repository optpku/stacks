/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite indexed families of generators of an ideal

`Ideal.FG` is intentionally existential.  This file supplies an explicit
finite-indexed presentation when a construction needs actual generators, while
keeping the noncanonical choice encapsulated in `FiniteGeneratingFamily.ofFG`.
-/

@[expose] public section

noncomputable section

universe u

namespace Ideal

variable {R : Type u} [Semiring R]

/-- The ideal of the list associated to a `Fin`-indexed family is the span of that family's
range. -/
@[stacks 00SC "finite family ideal/list span bridge"]
theorem ofList_ofFn_eq_span_range {c : ℕ} (xs : Fin c → R) :
    Ideal.ofList (List.ofFn xs) = Ideal.span (Set.range xs) := sorry

/-- An explicit finite family of elements of an ideal whose range spans that ideal. -/
structure FiniteGeneratingFamily (I : Ideal R) where
  /-- The number of chosen generators. -/
  count : ℕ
  /-- The chosen generator family. -/
  generator : Fin count → R
  /-- Every chosen generator lies in the ideal. -/
  generator_mem : ∀ i, generator i ∈ I
  /-- The chosen family spans the ideal. -/
  span_eq : Ideal.span (Set.range generator) = I

namespace FiniteGeneratingFamily

variable {I : Ideal R}

/-- The finite index type of a finite generating family. -/
abbrev Index (G : I.FiniteGeneratingFamily) : Type := Fin G.count

/-- The `i`-th element of a finite generating family belongs to the ideal. -/
theorem mem (G : I.FiniteGeneratingFamily) (i : G.Index) : G.generator i ∈ I := sorry

/-- The range of a finite generating family spans its ideal. -/
theorem span_range_eq (G : I.FiniteGeneratingFamily) :
    Ideal.span (Set.range G.generator) = I := sorry

/-- The generator function obtained by adjoining one element to a finite generating family. -/
def prependGenerator (G : I.FiniteGeneratingFamily) (a : I) : Fin (G.count + 1) → R :=
  Fin.cons (α := fun _ : Fin (G.count + 1) ↦ R) (a : R) G.generator

/-- Every value of the generator function obtained by adjoining an ideal element lies in the
ideal. -/
theorem prependGenerator_mem (G : I.FiniteGeneratingFamily) (a : I)
    (i : Fin (G.count + 1)) : prependGenerator G a i ∈ I := sorry

/-- Adjoining an ideal element to a spanning family leaves its generated ideal unchanged. -/
theorem span_range_prependGenerator (G : I.FiniteGeneratingFamily) (a : I) :
    Ideal.span (Set.range (prependGenerator G a)) = I := sorry

/-- Prepend an element of an ideal to an explicit finite generating family of that ideal. -/
@[stacks 00SC "prepend finite ideal generating family"]
def prepend (G : I.FiniteGeneratingFamily) (a : I) : I.FiniteGeneratingFamily where
  count := G.count + 1
  generator := prependGenerator G a
  generator_mem := prependGenerator_mem G a
  span_eq := span_range_prependGenerator G a

/-- A finite generating set selected from an `Ideal.FG` witness.

The selection is noncanonical; use `span_coe_finsetOfFG` and `finsetOfFG_mem`
rather than rely on a particular choice. -/
noncomputable def finsetOfFG (I : Ideal R) (hI : I.FG) : Finset R :=
  Classical.choose hI

/-- The finite set selected from an `Ideal.FG` witness spans the original ideal. -/
theorem span_coe_finsetOfFG (I : Ideal R) (hI : I.FG) :
    Ideal.span (↑(finsetOfFG I hI) : Set R) = I := sorry

/-- Every element of the finite set selected from an `Ideal.FG` witness lies in the ideal. -/
theorem finsetOfFG_mem (I : Ideal R) (hI : I.FG) {x : R}
    (hx : x ∈ finsetOfFG I hI) : x ∈ I := sorry

/-- Enumerating the selected finite generating set by `Fin` gives a family spanning the ideal. -/
theorem span_range_finsetOfFG (I : Ideal R) (hI : I.FG) :
    Ideal.span
        (Set.range fun i : Fin (finsetOfFG I hI).card ↦
          ((finsetOfFG I hI).equivFin.symm i : R)) =
      I := sorry

/-- A finite generating family selected from an `Ideal.FG` witness.

The data fields use only `finsetOfFG`; consumers should use `mem` and
`span_range_eq` rather than rely on a particular choice. -/
noncomputable def ofFG (I : Ideal R) (hI : I.FG) : I.FiniteGeneratingFamily where
  count := (finsetOfFG I hI).card
  generator := fun i ↦ (finsetOfFG I hI).equivFin.symm i
  generator_mem := fun i ↦
    finsetOfFG_mem I hI ((finsetOfFG I hI).equivFin.symm i).2
  span_eq := span_range_finsetOfFG I hI

/-- The generators selected by `ofFG` lie in the original ideal. -/
theorem ofFG_mem (I : Ideal R) (hI : I.FG) (i : (ofFG I hI).Index) :
    (ofFG I hI).generator i ∈ I := sorry

/-- The generators selected by `ofFG` span the original ideal. -/
theorem span_range_ofFG (I : Ideal R) (hI : I.FG) :
    Ideal.span (Set.range (ofFG I hI).generator) = I := sorry

end FiniteGeneratingFamily

end Ideal
