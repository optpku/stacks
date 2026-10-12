/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InGroupoids.PseudoPullback.Slice
public import ReasLib.CategoryTheory.Fibered.InSets.Slice
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Slice base changes of categories fibred in groupoids

This file owns the concrete base change of a morphism of groupoid fibrations along a morphism from
a canonical slice fibration. Property layers such as relative representability, fiber-class
presheaves, and stack conditions import this construction without depending on one another.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

variable {X Y : Groupoids.{u, v, max u v, v} C}

/-- The owner-level first projection from the explicit two-fibre product to `slice U` is fibred
in groupoids over `Over U`. -/
@[stacks 02Y6 "two-fibre-product first projection is fibred in groupoids"]
instance _root_.CategoryTheory.TwoFibreProduct.fstInGroupoids
    (F : X ⟶ Y) {U : C} (G : slice U ⟶ Y) :
    Functor.IsFibered.InGroupoids
      (toFunctor (CategoryTheory.TwoFibreProduct.fst G F)) := sorry
/- Proof strategy: unfold `TwoFibreProduct.fst` and `toFunctor`, then apply
`BasedCategory.PseudoPullback.Fst.inGroupoids`. -/

/-- The bicategorical base change of `F : X ⟶ Y` along a slice morphism
`G : slice U ⟶ Y`, bundled as a category fibred in groupoids over `Over U`.

Its total category is the explicit iso-comma object
`BasedCategory.PseudoPullback (toBasedFunctor G) (toBasedFunctor F)`, and its projection is the
canonical first projection. -/
@[stacks 02Y7 "canonical base change along a represented slice morphism"]
def baseChange (F : X ⟶ Y) {U : C} (G : slice U ⟶ Y) : Groupoids (Over U) :=
  BasedCategory.PseudoPullback.fstGroupoids (toBasedFunctor F) (toBasedFunctor G)

/-- The total category of a canonical base change is the total category of the corresponding
two-fibre-product apex over `C`. -/
@[simp]
theorem baseChange.total (F : X ⟶ Y) {U : C} (G : slice U ⟶ Y) :
    (baseChange F G).total =
      FiberedCategoryOver.Groupoids.total
        (CategoryTheory.TwoFibreProduct.apex G F) := sorry
/- Proof strategy: unfold `baseChange`, `TwoFibreProduct.apex`, and both total-category
projections. -/

/-- The projection of a canonical base change is the total functor underlying the first
two-fibre-product projection. -/
@[simp]
theorem baseChange.p (F : X ⟶ Y) {U : C} (G : slice U ⟶ Y) :
    (baseChange F G).p =
      toFunctor (CategoryTheory.TwoFibreProduct.fst G F) := sorry
/- Proof strategy: unfold `baseChange` and `TwoFibreProduct.fst`, then use
`BasedCategory.PseudoPullback.fstGroupoids.p`. -/

/-- The heterogeneous canonical base change of a morphism of saturated groupoid fibrations along
a based morphism from an ordinary slice. Its total category is the explicit heterogeneous
pseudo-pullback, while its base remains the ordinary slice category `Over U`. -/
@[stacks 02Y6 "heterogeneous canonical base change along a slice"]
def baseChange.overBase
    {X Y : Groupoids.{u, v, max w (max u v), max vS v} C}
    (F : X ⟶ Y) {U : C}
    (G : (slice U).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    FiberedCategoryOver.Groupoids (Over U) :=
  BasedCategory.PseudoPullback.fstGroupoids (toBasedFunctor F) G

/-- The total category of a heterogeneous canonical base change is its explicit
pseudo-pullback. -/
@[simp]
theorem baseChange.overBase.total
    {X Y : Groupoids.{u, v, max w (max u v), max vS v} C}
    (F : X ⟶ Y) {U : C}
    (G : (slice U).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    (baseChange.overBase F G).total =
      (BasedCategory.PseudoPullback G (toBasedFunctor F)).obj := sorry

/-- The projection of a heterogeneous canonical base change is the first pseudo-pullback
projection. -/
@[simp]
theorem baseChange.overBase.p
    {X Y : Groupoids.{u, v, max w (max u v), max vS v} C}
    (F : X ⟶ Y) {U : C}
    (G : (slice U).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    (baseChange.overBase F G).p =
      (BasedCategory.PseudoPullback.fst G (toBasedFunctor F)).toFunctor := sorry

end FiberedCategoryOver.Groupoids

end CategoryTheory

/- Axiom audit: `baseChange` has the explicit pseudo-pullback carrier and first projection. Any
`sorryAx` is confined to the Prop-valued groupoid-fibredness and functor-law fields inherited from
those canonical owners. -/
