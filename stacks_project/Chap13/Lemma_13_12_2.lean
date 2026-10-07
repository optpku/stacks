module

import ReasLib.CategoryTheory.DerivedCategory.ShortExact.TriangleMap
import StacksCheckRecall

@[expose] public section

/- Lemma 13.12.2 (`0153`): the isomorphism criterion for the canonical map between derived
triangles is owned by the neutral short-exact triangle API. -/
@[stacks 0153] #check
  @CategoryTheory.DerivedCategory.triangleOfSES.map_isIso_of_quasiIso
@[stacks 0153] #check
  @HomologicalComplex.HomologySequence.quasiIso_τ₃
