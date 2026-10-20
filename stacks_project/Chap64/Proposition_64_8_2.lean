module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.FilteredObject.FiniteDerived

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory (GradedObject ℤ A)]
  [HasDerivedCategory (GradedObject ℤ B)]

/- Proposition 64.8.2. In the situation of the filtered derived functor RT of a
left exact functor T : 𝒜 ⥤ₗ ℬ with enough injectives on 𝒜, the p-th associated-graded
functor commutes with RT: gr^p ∘ RT_filtered ≅ RT_ordinary ∘ gr^p as functors
DF⁺(𝒜) ⥤ D⁺(ℬ). -/
@[stacks 03TE] #check
  (CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact.GradedPiece.gradedPieceIso :
    ∀ (T : A ⥤ₗ B) [EnoughInjectives A] (p : ℤ),
      Plus.LeftExact.functor T (AssociatedGraded.inverts A) (AssociatedGraded.inverts B) ⋙
          Plus.GradedPiece.canonicalLift B p ≅
        Plus.GradedPiece.canonicalLift A p ⋙ T.obj.rightDerivedFunctorPlus)
