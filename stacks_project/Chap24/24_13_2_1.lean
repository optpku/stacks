module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import StacksCheckRecall

/-!
# The cohomology sequence attached to Lemma 24.13.2

The displayed four-term window and its exactness are the cochain specialization of Mathlib's
canonical long homology sequence for a short exact sequence of complexes.
-/

@[expose] public section

open CategoryTheory ComplexShape
open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (n : ℤ)

/- The five-arrow cohomology window is the canonical Mathlib construction. -/
#check @composableArrows₅

/- Its two adjacent exactness statements are owned by the short-exact homology API. -/
#check @ShortComplex.ShortExact.homology_exact₂
#check @ShortComplex.ShortExact.homology_exact₃

/- The boundary map is the canonical connecting morphism. -/
#check @ShortComplex.ShortExact.δ

/- Lemma 24.13.2, cohomology-sequence companion (0FRJ): the displayed five-arrow cohomology
window is exact. -/
@[stacks 0FRJ "long exact cohomology sequence"]
#check
  (composableArrows₅_exact hS n (n + 1) (up_mk n (n + 1) rfl) :
    (composableArrows₅ hS n (n + 1) (up_mk n (n + 1) rfl)).Exact)

end


end CategoryTheory
