module

import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.Vanishing
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.13.8

Filtered truncations and their universal properties are owned by the neutral
`FilteredComplex.Replace` API.  The chapter entry only recalls the three source-facing
consequences of associated-graded cohomology vanishing.
-/

/- Lemma 13.13.8 (1): lower associated-graded cohomology vanishing gives a finite filtered
replacement whose underlying complex is strictly bounded below. -/
@[stacks 05S5] #check
  @CategoryTheory.FilteredComplex.Replace.GE.exists_of_vanishes

/- Lemma 13.13.8 (2): upper associated-graded cohomology vanishing gives a finite filtered
replacement whose underlying complex is strictly bounded above. -/
@[stacks 05S5] #check
  @CategoryTheory.FilteredComplex.Replace.LE.exists_of_vanishes

/- Lemma 13.13.8 (3): eventual associated-graded cohomology vanishing gives a bounded
comparison square of finite filtered replacements. -/
@[stacks 05S5] #check
  @CategoryTheory.FilteredComplex.Replace.Bounded.Model.exists_of_eventually_vanishes

/- The explicit bounded replacement owner exposes the three representatives, four maps,
commutative square, quasi-isomorphisms, and strict bounds through named projections. -/
@[stacks 05S5] #check
  @CategoryTheory.FilteredComplex.Replace.Bounded.Model

/- Compatibility bridge to the source-facing nested existential. -/
@[stacks 05S5] #check
  @CategoryTheory.FilteredComplex.Replace.Bounded.exists_of_eventually_vanishes
