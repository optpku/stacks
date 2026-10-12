/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.GenericPoints

/-!
# Locally Noetherian normalizations over a field

This leaf records the locally Noetherian instance for the normalization of a
locally algebraic scheme over a field.  Keeping it separate prevents later
normalization invariants from rebuilding the same local instance.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.Normalization

variable {k : Type u} [Field k]

/-- The normalization of a locally algebraic scheme over a field is locally
Noetherian. -/
instance instIsLocallyNoetherian
    (X : SchemeOverField k) [LocallyAlgebraic X] :
    IsLocallyNoetherian X.left.normalization := sorry

end AlgebraicGeometry.SchemeOverField.Normalization
