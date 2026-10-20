module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Equivalence

/-!
# Unit computations for the categorical-pullback diagonal equivalence

The explicit diagonal equivalence unit retains both pullback objects.  This leaf exposes its four
component formulas without exposing the private unit construction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe vA vB vC vD uA uB uC uD

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace CategoricalPullback.DiagonalComparison.equivalence

variable (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)

/-- The first component of the forward unit is the identity. -/
@[simp] theorem unitIso.hom.app.fst (X : F ⊡ G) :
    ((DiagonalComparison.equivalence F G H).unitIso.hom.app X).fst = 𝟙 X.fst := sorry

/-- The second component of the forward unit is the identity. -/
@[simp] theorem unitIso.hom.app.snd (X : F ⊡ G) :
    ((DiagonalComparison.equivalence F G H).unitIso.hom.app X).snd = 𝟙 X.snd := sorry

/-- The first component of the inverse unit is the identity. -/
@[simp] theorem unitIso.inv.app.fst (X : F ⊡ G) :
    ((DiagonalComparison.equivalence F G H).unitIso.inv.app X).fst = 𝟙 X.fst := sorry

/-- The second component of the inverse unit is the identity. -/
@[simp] theorem unitIso.inv.app.snd (X : F ⊡ G) :
    ((DiagonalComparison.equivalence F G H).unitIso.inv.app X).snd = 𝟙 X.snd := sorry

end CategoricalPullback.DiagonalComparison.equivalence

end CategoryTheory.Limits
