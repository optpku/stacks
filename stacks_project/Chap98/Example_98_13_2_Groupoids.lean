module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Example_98_13_2_Predicate

/-!
# Category fibred in groupoids for the Artin versality counterexample

The full subcategory of `(Sch / Spec(Λ))` consisting of schemes that admit an
affine open cover on which `HasF` holds, packaged as an object of `GroupoidsOver`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open ObjectProperty
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ArtinVersalityCounterexample

variable (k : Type u) [Field k]

/-- A scheme over `Spec(Λ)` is covered when it has an affine open cover on which
`HasF` holds. -/
def IsCovered : ObjectProperty (Over (baseScheme k)) :=
  fun T ↦ ∃ 𝒰 : T.left.AffineOpenCover.{u},
    ∀ j : 𝒰.I₀, HasF (algebraMapOfHom (𝒰.f j ≫ T.hom))

/-- Membership in `IsCovered` is the existence of an affine open cover whose
coordinate rings satisfy `HasF`. -/
theorem isCovered_iff (T : Over (baseScheme k)) :
    IsCovered k T ↔
      ∃ 𝒰 : T.left.AffineOpenCover.{u},
        ∀ j : 𝒰.I₀, HasF (algebraMapOfHom (𝒰.f j ≫ T.hom)) :=
  sorry

/-- The inclusion of schemes covered by `HasF` is fibred in groupoids over
`Over (Spec(Λ))`. -/
instance instIsFiberedInGroupoids_covered :
    Functor.IsFibered.InGroupoids (ObjectProperty.ι (IsCovered k)) :=
  sorry

/-- The category fibred in groupoids `X` of schemes over `Spec(Λ)` that admit an
affine open cover on which `HasF` holds. -/
def groupoids : GroupoidsOver (baseScheme k) :=
  FiberedCategoryOver.Groupoids.ofFunctor (ObjectProperty.ι (IsCovered k))

/-- The projection of `groupoids k` is the full-subcategory inclusion of
`IsCovered`. -/
theorem groupoids_p :
    (groupoids k).p = ObjectProperty.ι (IsCovered k) :=
  sorry

/-- `groupoids k` is the groupoid fibration associated to the inclusion of
`IsCovered`. -/
theorem groupoids_spec :
    groupoids k =
      FiberedCategoryOver.Groupoids.ofFunctor (ObjectProperty.ι (IsCovered k)) :=
  sorry

/-- `Spec(Λ)` is locally Noetherian. -/
instance instIsLocallyNoetherian_baseScheme : IsLocallyNoetherian (baseScheme k) :=
  sorry

/-- The structure morphism `U ⟶ Spec(Λ)` is locally of finite type. -/
instance instLocallyOfFiniteType_testToBase : LocallyOfFiniteType (testToBase k) :=
  sorry

/-- The structure morphism of `testOver k` is locally of finite type. -/
instance instLocallyOfFiniteType_testOverHom : LocallyOfFiniteType (testOver k).hom :=
  sorry

end AlgebraicGeometry.ArtinVersalityCounterexample
