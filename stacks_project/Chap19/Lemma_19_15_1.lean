module

public import ReasLib.CategoryTheory.DerivedCategory.BrownRepresentability.Grothendieck
import StacksCheckRecall

@[expose] public section

/-!
# Brown Representability for a Grothendieck Derived Category

The source statement is the Grothendieck specialization of the reusable Brown-set API.  It does
not pass through compact generation, which is not available for an arbitrary Grothendieck
abelian category.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{max u v} A] [IsGrothendieckAbelian.{max u v} A]

/- Lemma 19.15.1: a contravariant cohomological functor on `D(A)` which sends direct sums to
products is representable. -/
@[stacks 0F5X] #check
  fun (H : (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
      (hH : H.rightOp.IsHomological)
      [∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H] ↦
    (DerivedCategory.Brown.existsRepresentation H hH :
      ∃ X : DerivedCategory A, Nonempty (preadditiveYoneda.obj X ≅ H))
