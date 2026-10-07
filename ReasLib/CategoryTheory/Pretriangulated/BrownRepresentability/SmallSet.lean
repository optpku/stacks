module

public import Mathlib.Logic.Small.Set
public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability
import Mathlib.Tactic.CrossRefAttribute

/-!
# Brown representability from a small detecting set

The object type of a large category usually lives one universe above its hom types.  Brown
representability only needs coproducts indexed in the universe in which the chosen detecting
set is small.  This file keeps that indexing universe independent of the object universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u v₁ v₂ u₁ u₂

namespace CategoryTheory.BrownRepresentability.SmallSet

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{w} D]

/-- A Brown set that is small in the coproduct universe represents every contravariant
homological functor preserving products indexed in that universe. -/
@[stacks 0GYG "small-set representability criterion"]
theorem existsRepresentation
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) (hH : H.rightOp.IsHomological)
    [∀ J : Type w, PreservesLimitsOfShape (Discrete J) H]
    (hD : ∃ S : Set D, Small.{w} S ∧ BrownRepresentability.IsSet S) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

/-- Type-valued representability supplied by a Brown set small in the coproduct universe. -/
@[stacks 0GYG "small-set underlying representability"]
theorem isRepresentable
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) (hH : H.rightOp.IsHomological)
    [∀ J : Type w, PreservesLimitsOfShape (Discrete J) H]
    (hD : ∃ S : Set D, Small.{w} S ∧ BrownRepresentability.IsSet S) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := sorry

end CategoryTheory.BrownRepresentability.SmallSet

namespace CategoryTheory.Functor.Brown.SmallSet

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D'] [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [_root_.CategoryTheory.IsTriangulated D]
  [_root_.CategoryTheory.IsTriangulated D'] [HasCoproducts.{w} D]

/-- A triangulated functor preserving coproducts indexed in the universe of a small Brown set
is a left adjoint. -/
@[stacks 0GYH "small-set left-adjoint criterion"]
theorem isLeftAdjoint
    (F : D ⥤ D') [LocallySmall.{v₁} D'] [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : Set D, Small.{w} S ∧ BrownRepresentability.IsSet S) :
    F.IsLeftAdjoint := sorry

/-- A triangulated functor preserving coproducts indexed in the universe of a small Brown set
has a right adjoint with its canonical triangulated shift comparison. -/
@[stacks 0GYH "small-set triangulated-right-adjoint criterion"]
theorem hasTriangulatedRightAdjoint
    (F : D ⥤ D') [LocallySmall.{v₁} D'] [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F]
    (hD : ∃ S : Set D, Small.{w} S ∧ BrownRepresentability.IsSet S) :
    ∃ (G : D' ⥤ D) (adj : F ⊣ G),
      G.IsTriangulatedWith (adj.rightAdjointCommShift ℤ) := sorry

end CategoryTheory.Functor.Brown.SmallSet
