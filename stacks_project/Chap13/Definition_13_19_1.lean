module

import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution
import StacksCheckRecall

@[expose] public section

/- Definition 13.19.1: `CochainComplex.ProjectiveResolution K` is the shared owner for a
quasi-isomorphism from a bounded-above cochain complex of projective objects to the cochain
complex `K`.  This is distinct from mathlib's object-level
`CategoryTheory.ProjectiveResolution`. -/
@[stacks 0643] #check @CochainComplex.ProjectiveResolution
@[stacks 0643] #check @CategoryTheory.ProjectiveResolution
