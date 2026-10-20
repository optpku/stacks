module

public import ReasLib.CategoryTheory.Filtration.Complex.Realization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Single-row and single-column degeneration

A bounded convergent realization whose second page is concentrated in one row or one column has
only one graded piece in each relevant total degree.  The resulting comparison with the
cohomology of the underlying filtered complex is independent of any derived-functor
presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.SpectralSequence.Realization

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace PageTwo

/-- The second page of a realization is concentrated in row `q` when every entry off that row
is zero. -/
@[stacks 012U "second page concentrated in one row"]
def IsConcentratedInRow (S : Realization (C := C)) (q : ℤ) : Prop :=
  ∀ p q' : ℤ, q' ≠ q → IsZero ((S.sequence.page 2).X (p, q'))

/-- The second page of a realization is concentrated in column `p` when every entry off that
column is zero. -/
@[stacks 012U "second page concentrated in one column"]
def IsConcentratedInColumn (S : Realization (C := C)) (p : ℤ) : Prop :=
  ∀ p' q : ℤ, p' ≠ p → IsZero ((S.sequence.page 2).X (p', q))

end PageTwo

namespace Degeneration

/-- In a single-row realization, cohomology in total degree `p + q` is isomorphic to the unique
second-page entry in that degree. -/
@[stacks 012U "single-row degeneration"]
theorem row (S : Realization (C := C)) {q : ℤ}
    (h : PageTwo.IsConcentratedInRow S q) (p : ℤ) :
    IsIsomorphic (S.filtered.underlying.homology (p + q))
      ((S.sequence.page 2).X (p, q)) := sorry

/-- In a single-column realization, cohomology in total degree `p + q` is isomorphic to the
unique second-page entry in that degree. -/
@[stacks 012U "single-column degeneration"]
theorem column (S : Realization (C := C)) {p : ℤ}
    (h : PageTwo.IsConcentratedInColumn S p) (q : ℤ) :
    IsIsomorphic (S.filtered.underlying.homology (p + q))
      ((S.sequence.page 2).X (p, q)) := sorry

end Degeneration

end CategoryTheory.FilteredComplex.SpectralSequence.Realization
