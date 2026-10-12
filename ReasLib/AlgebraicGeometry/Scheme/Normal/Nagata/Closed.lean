/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Japanese
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Noetherian

@[expose] public section

/-!
# Closed-subscheme criterion for Nagata schemes
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- A locally Noetherian scheme is Nagata exactly when every integral closed
subscheme is Japanese. -/
@[stacks 033Y]
theorem nagata_iff_forall_integral_closedSubscheme_japanese :
    Nagata X ↔
      ∀ ⦃Z : Scheme.{u}⦄ (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z], IsJapanese Z := sorry

end AlgebraicGeometry.Scheme
