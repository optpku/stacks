/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Locally algebraic field-extension base change

This leaf owns the local-finite-type stability needed whenever a scheme over a
field is pulled back along a field extension.  It deliberately lives beside
the slice-category base-change construction rather than in a normalization
comparison module.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FieldExtension.Over

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Field extension preserves local algebraicity over the base field. -/
instance instLocallyAlgebraic
    (X : SchemeOverField k) [LocallyAlgebraic X] :
    LocallyAlgebraic (baseChange k K X) := sorry

end AlgebraicGeometry.FieldExtension.Over
