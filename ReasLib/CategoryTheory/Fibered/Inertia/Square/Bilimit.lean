/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Bilimit.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Bilimit.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Comparison

/-!
# Bilimit of the relative-inertia square

Aggregate for the canonical pseudo-pullback cone, its projections, and its
universal property. The aggregate also exports the comparison computation API
used to read the two routes of the square. Direct consumers can import
`Construction` or `Computations` independently when they only need the bilimit
layer.
-/

@[expose] public section

namespace CategoryTheory.BasedCategory.RelativeInertia.Square

end CategoryTheory.BasedCategory.RelativeInertia.Square
