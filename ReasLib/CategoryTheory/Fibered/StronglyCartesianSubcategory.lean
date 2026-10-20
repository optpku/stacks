module

public import Mathlib.CategoryTheory.Widesubcategory
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber.Cartesian
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Property
public import ReasLib.CategoryTheory.MorphismProperty.WideSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# The wide subcategory of strongly cartesian morphisms

For a functor `p : S ⥤ C`, the morphisms strongly cartesian over their own image form a
multiplicative morphism property.  Restricting `p` to the corresponding wide subcategory gives a
canonical category fibred in groupoids whenever `p` is fibred.

The construction below acts on objects and cartesian `1`-morphisms. It is deliberately not
packaged as a pseudofunctor on all of `FiberedCategoryOver C`: a general vertical `2`-morphism need
not have strongly cartesian components, so it need not restrict to the associated groupoids.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Functor IsStronglyCartesian

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

namespace Functor.IsStronglyCartesian

/-- The wide subcategory of `S` whose morphisms are strongly cartesian over their image under
`p`. -/
@[stacks 03WQ "strongly-cartesian wide subcategory"]
abbrev subcategory (p : S ⥤ C) :=
  WideSubcategory (property p)

/-- The restriction of `p` to its strongly cartesian wide subcategory. -/
@[stacks 03WQ "strongly-cartesian restricted projection"]
abbrev projection (p : S ⥤ C) :
    subcategory p ⥤ C :=
  wideSubcategoryInclusion (property p) ⋙ p

/-- A morphism in the strongly cartesian wide subcategory is a lift for the restricted projection
exactly when its underlying morphism is a lift for `p`. -/
@[stacks 03WQ "restricted projection lift criterion"]
theorem projection_isHomLift_iff
    (p : S ⥤ C) {x y : subcategory p}
    {f : p.obj x.obj ⟶ p.obj y.obj} {φ : x ⟶ y} :
    (projection p).IsHomLift f φ ↔
      p.IsHomLift f φ.hom := sorry
/- Proof strategy: in both directions use `IsHomLift.of_fac`; after unfolding `projection`, the
endpoint and factorization equations are the same. -/

/-- Every morphism of the strongly cartesian wide subcategory remains strongly cartesian for the
restricted projection. -/
@[stacks 03WQ "restricted projection strong-cartesian map"]
theorem projectionMap
    (p : S ⥤ C) {x y : subcategory p} (φ : x ⟶ y) :
    (projection p).IsStronglyCartesian
      ((projection p).map φ) φ := sorry
/- Proof strategy: apply the universal property of `φ.hom`, transfer lift conditions with
`projection_isHomLift_iff`, and use cancellation of strongly cartesian composites to show that the
unique ambient factor belongs to the wide subcategory. -/

/-- The restriction of a fibred functor to its strongly cartesian morphisms is fibred in
groupoids. -/
@[stacks 03WQ, instance]
theorem projectionInGroupoids
    (p : S ⥤ C) [p.IsFibered] :
    Functor.IsFibered.InGroupoids (projection p) := sorry
/- Proof strategy: choose strongly cartesian lifts from fibredness of `p`; they are morphisms of
`subcategory p`.  The theorem `projectionMap` makes every restricted morphism strongly cartesian,
which supplies `IsFibered.InGroupoids.iff_isFibered_allStronglyCartesian`. -/

end Functor.IsStronglyCartesian

namespace FiberedCategoryOver

/-- The associated groupoid of a fibred category, obtained by retaining all objects and only
the strongly cartesian morphisms. -/
@[stacks 03WQ "associated groupoid of a fibred category"]
def associatedGroupoid
    (X : FiberedCategoryOver.{u₁, v₁, u₂, v₂} C) :
    FiberedCategoryOver.Groupoids.{u₁, v₁, u₂, v₂} C :=
  FiberedCategoryOver.Groupoids.ofFunctor
    (Functor.IsStronglyCartesian.projection X.p)

namespace associatedGroupoid

/-- The projection of the associated groupoid is the restriction of the original projection to
strongly cartesian morphisms. -/
@[simp, stacks 03WQ "associated-groupoid projection readout"]
theorem p (X : FiberedCategoryOver.{u₁, v₁, u₂, v₂} C) :
    X.associatedGroupoid.p =
      Functor.IsStronglyCartesian.projection X.p := sorry

/-- The based functor including the associated groupoid into its ambient fibred category. -/
@[stacks 03WQ "associated groupoid based inclusion"]
def inclusionBased
    (X : FiberedCategoryOver.{u₁, v₁, u₂, v₂} C) :
    BasedFunctor
      ((FiberedCategoryOver.Groupoids.toFibered C).obj
        X.associatedGroupoid).toBasedCategory
      X.toBasedCategory where
  toFunctor := wideSubcategoryInclusion
    (Functor.IsStronglyCartesian.property X.p)
  w := rfl

namespace inclusionBased

/-- The associated-groupoid inclusion preserves strongly cartesian morphisms. -/
@[stacks 03WQ "associated-groupoid inclusion preserves strong cartesianness"]
theorem preservesStronglyCartesian
    (X : FiberedCategoryOver.{u₁, v₁, u₂, v₂} C) :
    BasedFunctor.PreservesStronglyCartesian (inclusionBased X) := sorry

end inclusionBased

/-- The canonical morphism from the associated groupoid, regarded as a fibred category, to the
original fibred category. -/
@[stacks 03WQ "associated groupoid inclusion"]
def inclusion
    (X : FiberedCategoryOver.{u₁, v₁, u₂, v₂} C) :
    (FiberedCategoryOver.Groupoids.toFibered C).obj
        X.associatedGroupoid ⟶ X :=
  FiberedCategoryOver.ofBasedFunctor (inclusionBased X)
    (inclusionBased.preservesStronglyCartesian X)

/-- The based functor underlying the associated-groupoid inclusion is the canonical wide
subcategory inclusion. -/
@[simp, stacks 03WQ "associated-groupoid inclusion based readout"]
theorem inclusion.toBasedFunctor
    (X : FiberedCategoryOver.{u₁, v₁, u₂, v₂} C) :
    FiberedCategoryOver.toBasedFunctor (inclusion X) =
      inclusionBased X := sorry

end associatedGroupoid

/- Data audit: `associatedGroupoid` uses the explicit strongly-cartesian wide subcategory.
`inclusionBased` is the canonical wide-subcategory inclusion over the base, and `inclusion`
only attaches its strongly-cartesian preservation proof. No object, morphism, or functor data are
selected by a proof placeholder. -/

end FiberedCategoryOver

namespace CartesianBasedFunctor.AssociatedGroupoid

variable {S₁ : Type u₂} {S₂ : Type u₃}
variable [Category.{v₂} S₁] [Category.{v₃} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- A cartesian based functor maps the strongly-cartesian morphism property of its source into
the corresponding property of its target. -/
@[stacks 03WQ "cartesian map preserves the strongly-cartesian property"]
theorem mapsProperty (F : CartesianBasedFunctor p₁ p₂) :
    Functor.IsStronglyCartesian.property p₁ ≤
      (Functor.IsStronglyCartesian.property p₂).inverseImage F.toFunctor := sorry

/-- The functor on strongly-cartesian wide subcategories induced by a universe-polymorphic
cartesian based functor. -/
@[stacks 03WQ "object-and-1-cell action on the strongly-cartesian core"]
def functor (F : CartesianBasedFunctor p₁ p₂) :
    Functor.IsStronglyCartesian.subcategory p₁ ⥤
      Functor.IsStronglyCartesian.subcategory p₂ :=
  MorphismProperty.WideSubcategory.restrict F.toFunctor (mapsProperty F)

namespace functor

/-- On objects, the strongly-cartesian-core functor is the underlying total functor. -/
@[simp, stacks 03WQ "strongly-cartesian core object computation"]
theorem obj_obj
    (F : CartesianBasedFunctor p₁ p₂)
    (X : Functor.IsStronglyCartesian.subcategory p₁) :
    ((functor F).obj X).obj = F.toFunctor.obj X.obj := sorry

/-- On morphisms, the strongly-cartesian-core functor is the underlying total functor. -/
@[simp, stacks 03WQ "strongly-cartesian core morphism computation"]
theorem map_hom
    (F : CartesianBasedFunctor p₁ p₂)
    {X Y : Functor.IsStronglyCartesian.subcategory p₁} (f : X ⟶ Y) :
    ((functor F).map f).hom = F.toFunctor.map f.hom := sorry

/-- The strongly-cartesian-core functor commutes strictly with the restricted projections to
the common base. -/
@[stacks 03WQ "strongly-cartesian core projection compatibility"]
theorem comp_projection (F : CartesianBasedFunctor p₁ p₂) :
    functor F ⋙ Functor.IsStronglyCartesian.projection p₂ =
      Functor.IsStronglyCartesian.projection p₁ := sorry

end functor

/-- The functor on strongly-cartesian cores, bundled as a functor over the common base. -/
@[stacks 03WQ "based 1-cell action on the associated groupoid"]
def basedFunctor (F : CartesianBasedFunctor p₁ p₂) :
    BasedCategory.ofFunctor (Functor.IsStronglyCartesian.projection p₁) ⥤ᵇ
      BasedCategory.ofFunctor (Functor.IsStronglyCartesian.projection p₂) where
  toFunctor := functor F
  w := functor.comp_projection F

namespace basedFunctor

/-- Forgetting the based structure recovers the strongly-cartesian-core functor. -/
@[simp, stacks 03WQ "based strongly-cartesian core readout"]
theorem toFunctor (F : CartesianBasedFunctor p₁ p₂) :
    (basedFunctor F).toFunctor = functor F := sorry

end basedFunctor

end CartesianBasedFunctor.AssociatedGroupoid

namespace FiberedCategoryOver.associatedGroupoid

variable {X Y : FiberedCategoryOver.{u₁, v₁, u₂, v₂} C}

/-- A morphism of fibred categories induces a morphism between their associated groupoids. The
underlying total functor is the restriction of the original functor to strongly-cartesian
morphisms. This is the `1`-morphism action; no action on arbitrary vertical `2`-morphisms is
asserted. -/
@[stacks 03WQ "1-cell action on associated groupoids"]
def map (F : X ⟶ Y) : X.associatedGroupoid ⟶ Y.associatedGroupoid :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (CartesianBasedFunctor.AssociatedGroupoid.basedFunctor
      (FiberedCategoryOver.toCartesianBasedFunctor F))

/-- Forgetting an associated-groupoid map gives the canonical based restriction. -/
@[simp, stacks 03WQ "associated-groupoid map based readout"]
theorem map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (map F) =
      CartesianBasedFunctor.AssociatedGroupoid.basedFunctor
        (FiberedCategoryOver.toCartesianBasedFunctor F) := sorry

/-- The total functor of an associated-groupoid map is the restriction of the original total
functor to strongly-cartesian morphisms. -/
@[simp, stacks 03WQ "associated-groupoid map total readout"]
theorem map.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor (map F) =
      CartesianBasedFunctor.AssociatedGroupoid.functor
        (FiberedCategoryOver.toCartesianBasedFunctor F) := sorry

/-- Associated-groupoid inclusions are natural with respect to morphisms of fibred categories. -/
@[stacks 03WQ "associated-groupoid inclusion naturality"]
theorem inclusion_naturality (F : X ⟶ Y) :
    (FiberedCategoryOver.Groupoids.toFibered C).map (map F) ≫ inclusion Y =
      inclusion X ≫ F := sorry

/-- The associated-groupoid map of an identity morphism is the identity. -/
@[simp, stacks 03WQ "associated-groupoid map identity"]
theorem map_id (X : FiberedCategoryOver.{u₁, v₁, u₂, v₂} C) :
    map (𝟙 X) = 𝟙 X.associatedGroupoid := sorry

/-- Associated-groupoid maps preserve composition. -/
@[simp, stacks 03WQ "associated-groupoid map composition"]
theorem map_comp
    {Z : FiberedCategoryOver.{u₁, v₁, u₂, v₂} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) = map F ≫ map G := sorry

end FiberedCategoryOver.associatedGroupoid

end CategoryTheory
