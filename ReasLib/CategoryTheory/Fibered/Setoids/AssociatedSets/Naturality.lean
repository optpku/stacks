/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.Setoids.AssociatedSets.Comparison
public import ReasLib.CategoryTheory.Fibered.Setoids.Components.Grothendieck
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of the associated-sets comparison

The canonical comparison from a category fibred in setoids to its associated category fibred in
sets is natural in morphisms.  The component below is explicit: its base isomorphism comes from the
strict equation carried by the morphism over the base, and its category-of-elements arrow does not
choose representatives of fibrewise isomorphism classes.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

namespace toAssociatedSets.naturalityIso

/-- The base isomorphism underlying associated-sets naturality at a total object.  It is transport
along the strict equation saying that the given morphism lies over the identity of the base. -/
@[stacks 0432 "associated-sets naturality base isomorphism"]
noncomputable def baseIso
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (x : X.total) :
    (unop ((FiberedCategoryOver.Setoids.toFunctor
      (F ≫ Y.toAssociatedSets)).obj x)).fst ≅
      (unop ((FiberedCategoryOver.Setoids.toFunctor
        (X.toAssociatedSets ≫
          (FiberedCategoryOver.Sets.toSetoids C).map
            (components.mapHom F))).obj x)).fst :=
  eqToIso (congrArg (fun p : X.total ⥤ C => op (p.obj x))
    (FiberedCategoryOver.Setoids.comm F))

/-- The base isomorphism identifies the two fibrewise isomorphism classes occurring in the
associated-sets naturality component. -/
@[stacks 0432 "associated-sets naturality base compatibility"]
theorem baseIso.map_snd
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (x : X.total) :
    (Functor.fiberIsoClassPresheaf Y.p).map (baseIso F x).hom
        (unop ((FiberedCategoryOver.Setoids.toFunctor
          (F ≫ Y.toAssociatedSets)).obj x)).snd =
      (unop ((FiberedCategoryOver.Setoids.toFunctor
        (X.toAssociatedSets ≫
          (FiberedCategoryOver.Sets.toSetoids C).map
            (components.mapHom F))).obj x)).snd := sorry

/-- The explicit objectwise category-of-elements isomorphism comparing the two routes from `X`
to the setoid image of `Y.associatedSets`. -/
@[stacks 0432 "associated-sets naturality component"]
noncomputable def component
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (x : X.total) :
    (FiberedCategoryOver.Setoids.toFunctor
      (X.toAssociatedSets ≫
        (FiberedCategoryOver.Sets.toSetoids C).map (components.mapHom F))).obj x ≅
      (FiberedCategoryOver.Setoids.toFunctor (F ≫ Y.toAssociatedSets)).obj x :=
  Iso.op (CategoryOfElements.isoMk _ _ (baseIso F x) (baseIso.map_snd F x))

/-- The explicit associated-sets comparison components are natural in total-category
morphisms. -/
@[stacks 0432 "associated-sets naturality component naturality"]
theorem component.naturality
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y)
    {x y : X.total} (f : x ⟶ y) :
    (FiberedCategoryOver.Setoids.toFunctor
      (X.toAssociatedSets ≫
        (FiberedCategoryOver.Sets.toSetoids C).map
          (components.mapHom F))).map f ≫
        (component F y).hom =
      (component F x).hom ≫
        (FiberedCategoryOver.Setoids.toFunctor
          (F ≫ Y.toAssociatedSets)).map f := sorry

/-- Every associated-sets naturality component lies over the identity of the base. -/
@[stacks 0432 "associated-sets naturality component verticality"]
theorem component.isHomLift
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (x : X.total) :
    ((FiberedCategoryOver.Sets.toSetoids C).obj Y.associatedSets).p.IsHomLift
      (𝟙 (X.p.obj x)) (component F x).hom := sorry

end toAssociatedSets.naturalityIso

/-- Naturality of the associated-sets comparison at the level of underlying based functors. -/
@[stacks 0432 "associated-sets based naturality"]
noncomputable def toAssociatedSets.basedNaturalityIso
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor
        (X.toAssociatedSets ≫
          (FiberedCategoryOver.Sets.toSetoids C).map (components.mapHom F)) ≅
      FiberedCategoryOver.Setoids.toBasedFunctor (F ≫ Y.toAssociatedSets) :=
  BasedNatIso.ofComponents
    (toAssociatedSets.naturalityIso.component F)
    (toAssociatedSets.naturalityIso.component.naturality F)
    (toAssociatedSets.naturalityIso.component.isHomLift F)

/-- The canonical comparison with associated sets is natural in morphisms of categories fibred in
setoids. -/
@[stacks 0432 "naturality of the associated-sets comparison"]
noncomputable def toAssociatedSets.naturalityIso
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) :
    X.toAssociatedSets ≫
        (FiberedCategoryOver.Sets.toSetoids C).map (components.mapHom F) ≅
      F ≫ Y.toAssociatedSets :=
  FiberedCategoryOver.Setoids.BasedFunctorIso.lift
    (toAssociatedSets.basedNaturalityIso F)

namespace toAssociatedSets.naturalityIso

/-- The forward component of associated-sets naturality is the explicit category-of-elements
component. -/
@[simp, stacks 0432 "associated-sets naturality forward component"]
theorem hom.app
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (x : X.total) :
    (FiberedCategoryOver.Setoids.toBasedFunctorIso
      (toAssociatedSets.naturalityIso F)).hom.toNatTrans.app x =
        (component F x).hom := sorry

/-- The inverse component of associated-sets naturality is the inverse explicit
category-of-elements component. -/
@[simp, stacks 0432 "associated-sets naturality inverse component"]
theorem inv.app
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (x : X.total) :
    (FiberedCategoryOver.Setoids.toBasedFunctorIso
      (toAssociatedSets.naturalityIso F)).inv.toNatTrans.app x =
        (component F x).inv := sorry

end toAssociatedSets.naturalityIso

/- Axiom audit: `baseIso` is transport along the caller-supplied strict base equation, and
`component` is the explicit `CategoryOfElements.isoMk`.  Deferred dependencies occur only in the
quotient-value compatibility, naturality, verticality, and inverse-law proof fields. -/

end FiberedCategoryOver.Setoids

end CategoryTheory
