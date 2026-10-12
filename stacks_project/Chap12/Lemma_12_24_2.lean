/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
import StacksCheckRecall

/-!
# The Spectral Sequence of a Filtered Complex

The reusable all-page association relation, its explicit `Zᵣ/Bᵣ` representatives, and the
zeroth- and first-page comparison API are owned by
`ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence`.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : FilteredComplex C)

/- Lemma 12.24.2 (012M): every filtered complex admits an associated cohomological spectral
sequence whose pages are the explicit `Zᵣ/Bᵣ` subquotients and whose page differentials are
induced by the differential of the filtered complex. -/
@[stacks 012M "spectral sequence associated to a filtered complex"]
#check (FilteredComplex.IsAssociated.exists K :
  ∃ E : CohomologicalSpectralSequence C 0, FilteredComplex.IsAssociated K E)

#check FilteredComplex.Page.Zero.Comparison

#check FilteredComplex.Association.pageOneIso
