/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.FiberObject.Basic
public import ReasLib.CategoryTheory.Fibered.Setoids.FromSets

/-!
# Fibers of the inclusion from sets to setoids

This leaf supplies the presheaf-level naturality API for the canonical fiber
transport induced by `FiberedCategoryOver.Sets.toSetoids`.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

/-- The transport equivalences for `toSetoids` commute with the canonical fiber-object
presheaf restrictions. -/
theorem toSetoids.fiberEquiv.naturality
    (X : FiberedCategoryOver.Sets C) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((toSetoids C).obj X).toBasedCategory.p.fiberObjectPresheaf.map f ≫
        (Equiv.toIso (toSetoids.fiberEquiv X (unop V))).hom =
      (Equiv.toIso (toSetoids.fiberEquiv X (unop U))).hom ≫
        X.p.fiberObjectPresheaf.map f := sorry
/- Proof strategy: transport the canonical pullback action through
`toSetoids.obj.toBasedCategory`; both projections are the same functor over the base. -/

end FiberedCategoryOver.Sets

end CategoryTheory
