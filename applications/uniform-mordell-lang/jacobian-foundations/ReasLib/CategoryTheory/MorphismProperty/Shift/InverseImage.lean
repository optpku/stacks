module

public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Shift Compatibility of Inverse-Image Morphism Properties

Shift compatibility pulls back along any functor commuting with the same shift action.  Stability
under isomorphism absorbs the functor's comparison isomorphisms, so no fullness or faithfulness
assumption is needed.
-/

universe v₁ v₂ u₁ u₂ w

namespace CategoryTheory.MorphismProperty.IsCompatibleWithShift

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  {A : Type w} [AddMonoid A] [HasShift C A] [HasShift D A]

/-- the inverse image of a shift-compatible morphism property along a functor
commuting with shifts is shift-compatible. -/
@[stacks 0GSL "shift compatibility under inverse image"]
instance inverseImage (W : MorphismProperty D) (F : C ⥤ D)
    [W.IsCompatibleWithShift A] [W.RespectsIso] [F.CommShift A] :
    (W.inverseImage F).IsCompatibleWithShift A := sorry


end CategoryTheory.MorphismProperty.IsCompatibleWithShift
