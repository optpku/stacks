/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Fibered.InSets.Hom
public import ReasLib.CategoryTheory.Fibered.Setoids.Hom

/-!
# Forgetting discrete fibres to setoid fibres

The canonical property-inclusion pseudofunctor from categories fibred in sets to categories
fibred in setoids, with object, morphism, and fibre computation APIs.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

/-- Being fibred in sets implies being fibred in setoids as an inequality of the canonical
object properties on `BasedCategory C`. -/
theorem isFiberedInSets.le_isFiberedInSetoids :
    (isFiberedInSets C : ObjectProperty (BasedCategory.{vS, w} C)) ≤
      (isFiberedInSetoids C : ObjectProperty (BasedCategory.{vS, w} C)) := sorry
/- Proof strategy: apply the canonical `Functor.IsDiscreteFibration.inSetoids` instance to each
projection. -/

end BasedCategory

namespace FiberedCategoryOver.Sets

variable (C) in
/-- Forget discreteness from a category fibred in sets. Unlike an object coercion, this strict
pseudofunctor acts canonically on objects, `1`-morphisms, and `2`-morphisms. -/
def toSetoids : StrictPseudofunctor
    (FiberedCategoryOver.Sets.{u, v, w, vS} C) (FiberedCategoryOver.Setoids.{u, v, w, vS} C) :=
  FullSubbicategory.ιOfLE BasedCategory.isFiberedInSets.le_isFiberedInSetoids

/-- Forgetting the set-valued owner property leaves the underlying based category unchanged. -/
@[simp]
theorem toSetoids.obj.toBasedCategory (X : FiberedCategoryOver.Sets C) :
    ((toSetoids C).obj X).toBasedCategory = X.toBasedCategory := sorry
/- Proof strategy: use the object computation for `ObjectProperty.FullSubbicategory.ιOfLE`. -/

/-- The ambient based-functor representative of a morphism mapped by `toSetoids` is unchanged. -/
@[simp]
theorem toSetoids.map.hom
    {X Y : FiberedCategoryOver.Sets C} (F : X ⟶ Y) :
    ((toSetoids C).map F).hom = F.hom := sorry
/- Proof strategy: specialize `ObjectProperty.FullSubbicategory.ιOfLE.map`. -/

/-- The based-functor view of a morphism mapped by `toSetoids` is the original based functor. -/
@[simp]
theorem toSetoids.map.toBasedFunctor
    {X Y : FiberedCategoryOver.Sets C} (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor ((toSetoids C).map F) =
      FiberedCategoryOver.Sets.toBasedFunctor F := sorry
/- Proof strategy: unfold the two owner projections and apply `toSetoids.map.hom`. -/

/-- The total-category functor of a morphism mapped by `toSetoids` is the original total functor. -/
@[simp]
theorem toSetoids.map.toFunctor
    {X Y : FiberedCategoryOver.Sets C} (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toFunctor ((toSetoids C).map F) =
      FiberedCategoryOver.Sets.toFunctor F := sorry
/- Proof strategy: apply `congrArg BasedFunctor.toFunctor` to `toSetoids.map.toBasedFunctor F`. -/

/-- The ambient based natural transformation representative of a `2`-morphism mapped by
`toSetoids` is unchanged. -/
@[simp]
theorem toSetoids.map₂.hom
    {X Y : FiberedCategoryOver.Sets C} {F G : X ⟶ Y} (τ : F ⟶ G) :
    ((toSetoids C).map₂ τ).hom = τ.hom := sorry
/- Proof strategy: specialize `ObjectProperty.FullSubbicategory.ιOfLE.map₂`. -/

/-- The standard fibers of an object and of its image under `toSetoids` are canonically
identified. This is transport along `toSetoids.obj.toBasedCategory`, not a chosen equivalence. -/
noncomputable def toSetoids.fiberEquiv
    (X : FiberedCategoryOver.Sets C) (U : C) :
    ((toSetoids C).obj X).toBasedCategory.p.Fiber U ≃ X.p.Fiber U :=
  Equiv.cast <|
    congrArg (fun Y : BasedCategory.{vS, w} C => Y.p.Fiber U)
      (toSetoids.obj.toBasedCategory X)
/- Axiom audit: `Equiv.cast` has no choice-dependent data. The only deferred dependency is the
Prop-valued equality used for transport. -/

/-- The forward map of `toSetoids.fiberEquiv` is exactly transport along the unchanged based
category. -/
@[simp]
theorem toSetoids.fiberEquiv.apply
    (X : FiberedCategoryOver.Sets C) (U : C)
    (x : ((toSetoids C).obj X).toBasedCategory.p.Fiber U) :
    toSetoids.fiberEquiv X U x =
      Equiv.cast
        (congrArg (fun Y : BasedCategory.{vS, w} C => Y.p.Fiber U)
          (toSetoids.obj.toBasedCategory X)) x := sorry

/-- The inverse map of `toSetoids.fiberEquiv` is inverse transport along the unchanged based
category. -/
@[simp]
theorem toSetoids.fiberEquiv.symm_apply
    (X : FiberedCategoryOver.Sets C) (U : C) (x : X.p.Fiber U) :
    (toSetoids.fiberEquiv X U).symm x =
      (Equiv.cast
        (congrArg (fun Y : BasedCategory.{vS, w} C => Y.p.Fiber U)
          (toSetoids.obj.toBasedCategory X))).symm x := sorry

/-- The image of a category fibred in sets under `toSetoids` retains its discrete-fibration
property. This specific-image instance keeps the original fibre API available after forgetting
the owner property. -/
instance toSetoids.obj.isDiscreteFibration (X : FiberedCategoryOver.Sets C) :
    Functor.IsDiscreteFibration ((toSetoids C).obj X).p := X.property

end FiberedCategoryOver.Sets

end CategoryTheory
