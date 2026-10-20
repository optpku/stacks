module

import Mathlib.CategoryTheory.Triangulated.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.15

The reduced octahedron criterion belongs to Mathlib's canonical
`CategoryTheory.IsTriangulated` constructor.  It takes a replacement of an
arbitrary composable pair by an isomorphic pair together with distinguished
triangles and an octahedron for that replacement.
-/

namespace CategoryTheory

@[stacks 014C] #check @IsTriangulated.mk'

end CategoryTheory
