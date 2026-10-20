module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Squares of exact derived functors

An isomorphism between two composites of exact functors induces the corresponding isomorphism on
unbounded derived categories.  This is the unbounded companion of the bounded-below square owner;
the square is separated from any site, ring, or geometric presentation.
-/

open CategoryTheory

noncomputable section

universe uA uB uC uD vA vB vC vD wA wB wC wD

namespace CategoryTheory.ExactFunctor.MapDerivedCategory

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable [Abelian A] [Abelian B] [Abelian C] [Abelian D]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

/-- The derived square induced by an isomorphism
`F.comp G ≅ H.comp I` of exact-functor composites. -/
@[stacks 015F "square of unbounded exact derived functors"]
noncomputable def squareIso
    (F : A ⥤ₑ B) (G : B ⥤ₑ D) (H : A ⥤ₑ C) (I : C ⥤ₑ D)
    (e : F.comp G ≅ H.comp I) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ I.mapDerivedCategory :=
  (compFunctorIso F G).symm ≪≫ ExactFunctor.MapDerivedCategory.mapIso e ≪≫
    compFunctorIso H I

end CategoryTheory.ExactFunctor.MapDerivedCategory

end
