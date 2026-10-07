module

public import ReasLib.AlgebraicTopology.SimplicialSet.Subcomplex.Filtration.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
import StacksCheckRecall

/-!
@stack 018S

# Source-facing bridge for Lemma 14.21.8

The attachment relation and its finite filtration theorem are owned by
`SSet.Subcomplex` in ReasLib.
-/

@[expose] public section

open CategoryTheory

universe u

namespace SSet

variable {V : SSet.{u}} [V.Finite] [V.Nonempty]
variable (U : V.Subcomplex) [(U : SSet).Nonempty]

/- Lemma 14.21.8: a finite simplicial set is obtained from any subcomplex by a finite sequence of
single-simplex extensions. -/
@[stacks 018S]
#check (Subcomplex.singleSimplex.existsFiltration U :
  ∃ F : Subcomplex.singleSimplex.Filtration V,
  F.head = U ∧ F.last = (⊤ : V.Subcomplex))

#check Subcomplex.singleSimplex.Filtration.attachment
#check Subcomplex.singleSimplex.Filtration.cons
#check Subcomplex.singleSimplex.Filtration.toRelSeries
#check Subcomplex.singleSimplex.existsRelSeries U
#check Subcomplex.singleSimplex.extensionRel V

end SSet
