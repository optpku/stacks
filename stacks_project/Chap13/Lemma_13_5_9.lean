/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.MorphismProperty.Localization.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.5.9

The chapter statement is the source-facing recall of the general zero-object criteria for a
triangulation-compatible localization.
-/

open CategoryTheory CategoryTheory.Limits MorphismProperty Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (S : MorphismProperty D) [S.IsCompatibleWithTriangulation] (Z : D)

section

variable [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]

/- Lemma 13.5.9 (1) (`05R8`): an object becomes zero after localization exactly when it is a
retract of the third vertex of a distinguished triangle whose first morphism is inverted. -/
@[stacks 05R8] #check
  (MorphismProperty.Localization.objectIsZero_tfae_of_compatibleWithTriangulation S Z :
    List.TFAE
      [ IsZero (S.Q.obj Z)
      , ∃ Z' : D, S (0 : Z ⟶ Z')
      , ∃ Z' : D, S (0 : Z' ⟶ Z)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
      ])

end

section

variable [S.IsSaturatedMultiplicativeSystem]

/- Lemma 13.5.9 (2) (`05R8`): under saturation, the same criterion is equivalent to the two
canonical zero denominators and to a distinguished triangle with third vertex exactly `Z`. -/
@[stacks 05R8] #check
  (MorphismProperty.Localization.objectIsZero_tfae_of_saturated_compatibleWithTriangulation S Z :
    List.TFAE
      [ IsZero (S.Q.obj Z)
      , ∃ Z' : D, S (0 : Z ⟶ Z')
      , ∃ Z' : D, S (0 : Z' ⟶ Z)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
      , S (0 : 0 ⟶ Z)
      , S (0 : Z ⟶ 0)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ T.obj₃ = Z
      ])

end

end

end CategoryTheory
