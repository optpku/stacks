/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Equivalence

/-!
# Counit computations for the categorical-pullback diagonal equivalence

The explicit counit retains the two inner objects and uses the first projection of the outer
pullback isomorphism on the common base object.  These formulas form the public rewriting surface.
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

/-- The first inner component of the forward counit is the identity. -/
@[simp] theorem counitIso.hom.app.fstFst
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    ((DiagonalComparison.equivalence F G H).counitIso.hom.app X).fst.fst =
      𝟙 X.fst.fst := sorry

/-- The second inner component of the forward counit is the identity. -/
@[simp] theorem counitIso.hom.app.fstSnd
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    ((DiagonalComparison.equivalence F G H).counitIso.hom.app X).fst.snd =
      𝟙 X.fst.snd := sorry

/-- The outer component of the forward counit is the first projection of the structural
isomorphism. -/
@[simp] theorem counitIso.hom.app.snd
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    ((DiagonalComparison.equivalence F G H).counitIso.hom.app X).snd =
      ((π₁ H H).mapIso X.iso).hom := sorry

/-- The first inner component of the inverse counit is the identity. -/
@[simp] theorem counitIso.inv.app.fstFst
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    ((DiagonalComparison.equivalence F G H).counitIso.inv.app X).fst.fst =
      𝟙 X.fst.fst := sorry

/-- The second inner component of the inverse counit is the identity. -/
@[simp] theorem counitIso.inv.app.fstSnd
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    ((DiagonalComparison.equivalence F G H).counitIso.inv.app X).fst.snd =
      𝟙 X.fst.snd := sorry

/-- The outer component of the inverse counit is the inverse first projection of the structural
isomorphism. -/
@[simp] theorem counitIso.inv.app.snd
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    ((DiagonalComparison.equivalence F G H).counitIso.inv.app X).snd =
      ((π₁ H H).mapIso X.iso).inv := sorry

end CategoricalPullback.DiagonalComparison.equivalence

end CategoryTheory.Limits
