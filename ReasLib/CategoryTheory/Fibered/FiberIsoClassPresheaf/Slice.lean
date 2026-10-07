module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Slice.Cartesian
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber-class presheaves on slice base changes

This file owns the presheaf of fiberwise isomorphism classes attached to a slice base change of a
groupoid-fibred morphism. It also separates two reusable quantifier patterns: a property may hold
after every slice base change, or after a slice representative of every target-fiber object.
The comparison is formulated for an arbitrary isomorphism-invariant object property, so
representability and the sheaf condition use the same Yoneda and base-change infrastructure.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

namespace FiberedCategoryOver.Groupoids.Hom

/-- The presheaf of isomorphism classes in the base change of `F` along a morphism from the
canonical groupoid-fibred slice over `U`. -/
noncomputable def sliceFiberClasses
    (F : X ⟶ Y) {U : C} (G : slice U ⟶ Y) :
    (Over U)ᵒᵖ ⥤ Type (max u v) :=
  CartesianBasedFunctor.sliceFiberClasses
    (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor F)
    (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor G)

/-- The concrete fiber-pair presheaf attached to `F` and `y : Y.p.Fiber U`: take the canonical
selected-cleavage slice representative of `y`, base-change `F` along it, and pass to fiberwise
isomorphism classes. -/
noncomputable def fiberPairClasses
    (F : X ⟶ Y) {U : C} (y : Y.p.Fiber U) :
    (Over U)ᵒᵖ ⥤ Type (max u v) :=
  sliceFiberClasses F (YonedaSlice.representative y)

/-- An isomorphism-invariant property holds for the concrete fiber-pair presheaf exactly when it
holds for every slice representative whose identity-fiber value is isomorphic to `y`. -/
theorem fiberPairClasses.property_iff
    {U : C}
    (P : ObjectProperty ((Over U)ᵒᵖ ⥤ Type (max u v)))
    [hP : P.IsClosedUnderIsomorphisms]
    (F : X ⟶ Y) (y : Y.p.Fiber U) :
    P (fiberPairClasses F y) ↔
      ∀ (G : slice U ⟶ Y)
        (_ : (fiberFunctor G U).obj
          (BasedCategory.Yoneda.Identity.fiberObj U) ≅ y),
        P (sliceFiberClasses F G) := sorry

/-- An object property of slice presheaves holds after every canonical slice base change of
`F`. -/
def sliceFiberClasses.satisfies
    (P : ∀ U : C, ObjectProperty ((Over U)ᵒᵖ ⥤ Type (max u v)))
    (F : X ⟶ Y) : Prop :=
  ∀ {U : C} (G : slice U ⟶ Y), P U (sliceFiberClasses F G)

/-- An object property of slice presheaves holds on the concrete fiber-pair presheaf of every
object in every target fiber. For isomorphism-invariant properties,
`fiberPairClasses.property_iff` makes this independent of the selected cleavage representative. -/
def fiberPairClasses.satisfies
    (P : ∀ U : C, ObjectProperty ((Over U)ᵒᵖ ⥤ Type (max u v)))
    (F : X ⟶ Y) : Prop :=
  ∀ {U : C} (y : Y.p.Fiber U),
    P U (fiberPairClasses F y)

/-- For an isomorphism-invariant presheaf property, checking one slice representative of every
target-fiber object is equivalent to checking every slice morphism. -/
theorem fiberPairClasses.satisfies_iff_slice
    (P : ∀ U : C, ObjectProperty ((Over U)ᵒᵖ ⥤ Type (max u v)))
    [hP : ∀ U : C, (P U).IsClosedUnderIsomorphisms]
    (F : X ⟶ Y) :
    fiberPairClasses.satisfies P F ↔
      sliceFiberClasses.satisfies P F := sorry

/- Axiom audit: both fixed-universe data owners delegate to the heterogeneous cartesian owners.
Any `sorryAx` is confined to inherited Prop-valued fibredness, cartesianness, and functor laws. -/

end FiberedCategoryOver.Groupoids.Hom

end CategoryTheory
