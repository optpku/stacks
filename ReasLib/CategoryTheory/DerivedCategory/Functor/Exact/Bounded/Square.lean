module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Naturality
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Squares of bounded-below exact derived functors

An isomorphism between two composites of exact functors induces the corresponding square on
bounded-below derived categories.  The construction combines functoriality in exact natural
isomorphisms with the canonical composition comparisons.
-/

open CategoryTheory

noncomputable section

universe w uA uB uC uD vA vB vC vD

namespace CategoryTheory.ExactFunctor.Derived.Plus

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable [Abelian A] [Abelian B] [Abelian C] [Abelian D]
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]

/-- An isomorphism between two composites of exact functors induces the canonical square between
their bounded-below derived actions. -/
@[stacks 015F "square of bounded-below exact derived functors"]
noncomputable def squareIso
    (F : A ⥤ₑ B) (G : B ⥤ₑ D) (H : A ⥤ₑ C) (I : C ⥤ₑ D)
    (e : F.comp G ≅ H.comp I) :
    functor F ⋙ functor G ≅ functor H ⋙ functor I :=
  (compFunctorIso F G).symm ≪≫ mapIso e ≪≫ compFunctorIso H I

end CategoryTheory.ExactFunctor.Derived.Plus
