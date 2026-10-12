/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Preadditive
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem

/-!
# Zero Objects in Pretriangulated Localizations

This module extends the additive zero-object criteria for a localization by a morphism property
to pretriangulated categories.  It characterizes an object that becomes zero by a distinguished
triangle with a retract witness, and records the sharper saturated-system forms using the two
canonical zero morphisms and an exact third vertex.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.MorphismProperty.Localization

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable (W : MorphismProperty C) [W.IsCompatibleWithTriangulation]

/-- an object becomes zero after a pretriangulated localization exactly when it is
a retract of the third vertex of a distinguished triangle whose first morphism is inverted. -/
@[stacks 05R8 "zero objects in pretriangulated localizations"]
theorem objectIsZero_iff_exists_distinguished_retract
    [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions] (X : C) :
    IsZero (W.Q.obj X) ↔
      ∃ T : Triangle C, T ∈ distTriang C ∧ W T.mor₁ ∧ Nonempty (Retract X T.obj₃) := sorry

/-- for a saturated pretriangulated localization, an object becomes zero exactly
when the canonical zero morphism from the zero object to it is inverted. -/
@[stacks 05R8 "zero objects in saturated pretriangulated localizations"]
theorem objectIsZero_iff_zero_from_zero_mem
    [W.IsSaturatedMultiplicativeSystem] (X : C) :
    IsZero (W.Q.obj X) ↔ W (0 : 0 ⟶ X) := sorry

/-- for a saturated pretriangulated localization, an object becomes zero exactly
when the canonical zero morphism from it to the zero object is inverted. -/
@[stacks 05R8 "zero objects in saturated pretriangulated localizations"]
theorem objectIsZero_iff_zero_to_zero_mem
    [W.IsSaturatedMultiplicativeSystem] (X : C) :
    IsZero (W.Q.obj X) ↔ W (0 : X ⟶ 0) := sorry

/-- for a saturated pretriangulated localization, an object becomes zero exactly
when it is the third vertex of a distinguished triangle whose first morphism is inverted. -/
@[stacks 05R8 "zero objects in saturated pretriangulated localizations"]
theorem objectIsZero_iff_exists_distinguished_obj3_eq
    [W.IsSaturatedMultiplicativeSystem] (X : C) :
    IsZero (W.Q.obj X) ↔
      ∃ T : Triangle C, T ∈ distTriang C ∧ W T.mor₁ ∧ T.obj₃ = X := sorry

/-- the additive zero-object criteria and the distinguished-retract criterion are
equivalent for every triangulation-compatible localization with both fraction calculi. -/
@[stacks 05R8 "zero objects in pretriangulated localizations"]
theorem objectIsZero_tfae_of_compatibleWithTriangulation
    [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions] (X : C) :
    List.TFAE
      [ IsZero (W.Q.obj X)
      , ∃ Y : C, W (0 : X ⟶ Y)
      , ∃ Y : C, W (0 : Y ⟶ X)
      , ∃ T : Triangle C, T ∈ distTriang C ∧ W T.mor₁ ∧ Nonempty (Retract X T.obj₃)
      ] := sorry

/-- for a saturated triangulation-compatible localization, the zero-object
criterion is also equivalent to the two canonical zero denominators and to an exact third-vertex
distinguished triangle. -/
@[stacks 05R8 "zero objects in saturated pretriangulated localizations"]
theorem objectIsZero_tfae_of_saturated_compatibleWithTriangulation
    [W.IsSaturatedMultiplicativeSystem] (X : C) :
    List.TFAE
      [ IsZero (W.Q.obj X)
      , ∃ Y : C, W (0 : X ⟶ Y)
      , ∃ Y : C, W (0 : Y ⟶ X)
      , ∃ T : Triangle C, T ∈ distTriang C ∧ W T.mor₁ ∧ Nonempty (Retract X T.obj₃)
      , W (0 : 0 ⟶ X)
      , W (0 : X ⟶ 0)
      , ∃ T : Triangle C, T ∈ distTriang C ∧ W T.mor₁ ∧ T.obj₃ = X
      ] := sorry


end CategoryTheory.MorphismProperty.Localization
