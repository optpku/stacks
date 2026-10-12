/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Hom-stacks with scheme domain

The mapping stack `homStack X Z` of a scheme `X` over `S` into a category fibred in
groupoids `Z` over `S` is the category of pairs `(T, y)` with `y` an object of `Z`
over `X ×_S T`. Equivalently, the fibre over `T` is the category of 1-morphisms
`slice (X ×_S T) ⟶ Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The fibre product of two schemes over `S`, viewed as an object of `Over S`. -/
def testPullback {S : Scheme.{u}} (X T : Over S) : Over S :=
  X ⊗ T

/-- Unfolding `testPullback` recovers the tensor product in `Over S`. -/
theorem testPullback_eq {S : Scheme.{u}} (X T : Over S) :
    testPullback X T = X ⊗ T := sorry

/-- The functor `T ↦ X ×_S T` on schemes over `S`. -/
def testPullbackFunctor {S : Scheme.{u}} (X : Over S) : Over S ⥤ Over S :=
  tensorLeft X

/-- The value of `testPullbackFunctor X` at `T` is `testPullback X T`. -/
theorem testPullbackFunctor_obj {S : Scheme.{u}} (X T : Over S) :
    (testPullbackFunctor X).obj T = testPullback X T := sorry

variable {S : Scheme.{u}}

/-- An object of the Hom-stack of morphisms from a scheme `X` over `S` to a
category fibred in groupoids `Z`: a test scheme `base` over `S` together with an
object of `Z` over `X ×_S base`. -/
structure HomObj (X : Over S) (Z : GroupoidsOver S) where
  /-- The underlying test scheme over `S`. -/
  base : Over S
  /-- The object of `Z` over `X ×_S base`. -/
  fiber : Z.p.Fiber (testPullback X base)

/-- Assemble an object of the Hom-stack from a test scheme and a fibre object of `Z`. -/
def HomObj.ofFiber {X : Over S} {Z : GroupoidsOver S} (T : Over S)
    (y : Z.p.Fiber (testPullback X T)) : HomObj X Z where
  base := T
  fiber := y

/-- The constructor of `HomObj` stores the supplied test scheme and fibre object. -/
theorem HomObj.ofFiber_spec {X : Over S} {Z : GroupoidsOver S} (T : Over S)
    (y : Z.p.Fiber (testPullback X T)) :
    (HomObj.ofFiber T y).base = T ∧ (HomObj.ofFiber T y).fiber = y := sorry

/-- The 1-morphism `slice (X ×_S base) ⟶ Z` classified by a Hom-stack object. -/
def HomObj.map {X : Over S} {Z : GroupoidsOver S} (ξ : HomObj X Z) :
    slice (testPullback X ξ.base) ⟶ Z :=
  FiberedCategoryOver.Groupoids.YonedaSlice.representative ξ.fiber

/-- `HomObj.map` is the Yoneda representative of the stored fibre object. -/
theorem HomObj.map_eq {X : Over S} {Z : GroupoidsOver S} (ξ : HomObj X Z) :
    HomObj.map ξ = FiberedCategoryOver.Groupoids.YonedaSlice.representative ξ.fiber :=
  sorry

/-- A morphism of Hom-stack objects: a map of test schemes and a lift in `Z`
over the induced map of fibre products. -/
structure HomObj.Hom {X : Over S} {Z : GroupoidsOver S} (ξ ξ' : HomObj X Z) where
  /-- The underlying morphism of test schemes over `S`. -/
  f : ξ.base ⟶ ξ'.base
  /-- The morphism in the total category of `Z`. -/
  φ : ξ.fiber.1 ⟶ ξ'.fiber.1
  /-- The morphism `φ` lies over `X ×_S f`. -/
  isHomLift : Z.p.IsHomLift ((testPullbackFunctor X).map f) φ

/-- Identity morphisms of Hom-stack objects lift the identity of the fibre product. -/
theorem HomObj.id_isHomLift {X : Over S} {Z : GroupoidsOver S} (ξ : HomObj X Z) :
    Z.p.IsHomLift ((testPullbackFunctor X).map (𝟙 ξ.base)) (𝟙 ξ.fiber.1) := sorry

/-- Identity morphisms of Hom-stack objects. -/
def HomObj.idHom {X : Over S} {Z : GroupoidsOver S} (ξ : HomObj X Z) : HomObj.Hom ξ ξ where
  f := 𝟙 ξ.base
  φ := 𝟙 ξ.fiber.1
  isHomLift := HomObj.id_isHomLift ξ

/-- Composite morphisms of Hom-stack objects lift the composite fibre-product map. -/
theorem HomObj.comp_isHomLift {X : Over S} {Z : GroupoidsOver S} {ξ ξ' ξ'' : HomObj X Z}
    (α : HomObj.Hom ξ ξ') (β : HomObj.Hom ξ' ξ'') :
    Z.p.IsHomLift ((testPullbackFunctor X).map (α.f ≫ β.f)) (α.φ ≫ β.φ) := sorry

/-- Composition of morphisms of Hom-stack objects. -/
def HomObj.compHom {X : Over S} {Z : GroupoidsOver S} {ξ ξ' ξ'' : HomObj X Z}
    (α : HomObj.Hom ξ ξ') (β : HomObj.Hom ξ' ξ'') : HomObj.Hom ξ ξ'' where
  f := α.f ≫ β.f
  φ := α.φ ≫ β.φ
  isHomLift := HomObj.comp_isHomLift α β

/-- Left identity law for morphisms of Hom-stack objects. -/
theorem HomObj.idHom_comp {X : Over S} {Z : GroupoidsOver S} {ξ ξ' : HomObj X Z}
    (α : HomObj.Hom ξ ξ') : HomObj.compHom (HomObj.idHom ξ) α = α := sorry

/-- Right identity law for morphisms of Hom-stack objects. -/
theorem HomObj.compHom_id {X : Over S} {Z : GroupoidsOver S} {ξ ξ' : HomObj X Z}
    (α : HomObj.Hom ξ ξ') : HomObj.compHom α (HomObj.idHom ξ') = α := sorry

/-- Associativity of composition of morphisms of Hom-stack objects. -/
theorem HomObj.assocHom {X : Over S} {Z : GroupoidsOver S} {ξ₁ ξ₂ ξ₃ ξ₄ : HomObj X Z}
    (α : HomObj.Hom ξ₁ ξ₂) (β : HomObj.Hom ξ₂ ξ₃) (γ : HomObj.Hom ξ₃ ξ₄) :
    HomObj.compHom (HomObj.compHom α β) γ = HomObj.compHom α (HomObj.compHom β γ) :=
  sorry

/-- The category of Hom-stack objects. -/
instance instCategoryHomObj (X : Over S) (Z : GroupoidsOver S) : Category (HomObj X Z) where
  Hom ξ ξ' := HomObj.Hom ξ ξ'
  id ξ := HomObj.idHom ξ
  comp α β := HomObj.compHom α β
  id_comp := HomObj.idHom_comp
  comp_id := HomObj.compHom_id
  assoc := HomObj.assocHom

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem homStackForget_map_id {X : Over S} {Z : GroupoidsOver S} (ξ : HomObj X Z) :
    (HomObj.idHom ξ).f = 𝟙 ξ.base := sorry

/-- The forgetful functor preserves composition. -/
theorem homStackForget_map_comp {X : Over S} {Z : GroupoidsOver S} {ξ ξ' ξ'' : HomObj X Z}
    (α : HomObj.Hom ξ ξ') (β : HomObj.Hom ξ' ξ'') :
    (HomObj.compHom α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor from the Hom-stack to `(Sch/S)_fppf`. -/
def homStackForget (X : Over S) (Z : GroupoidsOver S) : HomObj X Z ⥤ Over S where
  obj ξ := ξ.base
  map α := α.f
  map_id := homStackForget_map_id
  map_comp := homStackForget_map_comp

/-- The forgetful functor sends a Hom-stack object to its test scheme. -/
theorem homStackForget_obj {X : Over S} {Z : GroupoidsOver S} (ξ : HomObj X Z) :
    (homStackForget X Z).obj ξ = ξ.base := sorry

/-- The forgetful functor sends a Hom-stack morphism to its underlying scheme map. -/
theorem homStackForget_map {X : Over S} {Z : GroupoidsOver S} {ξ ξ' : HomObj X Z}
    (α : HomObj.Hom ξ ξ') : (homStackForget X Z).map α = α.f := sorry

/-- The forgetful functor of the Hom-stack is fibred in groupoids. -/
instance instIsFiberedInGroupoids_homStackForget (X : Over S) (Z : GroupoidsOver S) :
    Functor.IsFibered.InGroupoids (homStackForget X Z) := sorry

/-- The Hom-stack of morphisms from a scheme `X` over `S` to a category fibred in
groupoids `Z` over `S`. -/
def homStack (X : Over S) (Z : GroupoidsOver S) : GroupoidsOver S :=
  FiberedCategoryOver.Groupoids.ofFunctor (homStackForget X Z)

/-- The projection of `homStack X Z` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem homStack_p (X : Over S) (Z : GroupoidsOver S) :
    (homStack X Z).p = homStackForget X Z := sorry

/-- Objects of `homStack X Z` over `T` are Hom-stack objects with base `T` and
fibre object of `Z` over `X ×_S T`. -/
theorem homStack_fibre (X : Over S) (Z : GroupoidsOver S) (T : Over S)
    (ξ : HomObj X Z) :
    (homStack X Z).p.obj ξ = T ↔
      ∃ y : Z.p.Fiber (testPullback X T), ξ = HomObj.ofFiber T y := sorry

/-- Equivalently, an object of `Z` over `X ×_S T` classifies a 1-morphism
`slice (X ×_S T) ⟶ Z` and determines an object of `homStack X Z` over `T`. -/
theorem homStack_fibre_hom (X : Over S) (Z : GroupoidsOver S) (T : Over S)
    (y : Z.p.Fiber (testPullback X T)) :
    (homStack X Z).p.obj (HomObj.ofFiber T y) = T ∧
      HomObj.map (HomObj.ofFiber T y) =
        FiberedCategoryOver.Groupoids.YonedaSlice.representative y := sorry

end AlgebraicGeometry.GroupoidsOver
