/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- `FullyFaithful` occurs in the exported structure of the identity-comparison inclusion.
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Projections

/-!
# Identity-comparison inclusion for adjoint factorization

This leaf owns the fully faithful inclusion of the source into the vertical-comma
middle category and its computation formulas.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory
open scoped Bicategory

universe u v w

namespace CategoryTheory.FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, w} C}

noncomputable section

namespace AdjointFactorization

namespace Implementation

/-- The comma object whose comparison arrow is `𝟙 (F.obj x)`. -/
private def inclusionCommaObj (F : X ⟶ Y) (x : X.total) :
    Comma (𝟭 Y.total) (toFunctor F) where
  left := (toFunctor F).obj x
  right := x
  hom := 𝟙 _

/-- The identity comparison squares commute. -/
private theorem inclusionCommaMap_comm (F : X ⟶ Y) {x x' : X.total} (f : x ⟶ x') :
    (𝟭 Y.total).map ((toFunctor F).map f) ≫ (inclusionCommaObj F x').hom =
      (inclusionCommaObj F x).hom ≫ (toFunctor F).map f := sorry
/- Proof strategy: unfold `inclusionCommaObj`; functoriality of the identity functor and the
left/right identity laws reduce both sides to `(toFunctor F).map f`. -/

/-- The comma morphism induced by a morphism of `X.total`. -/
private def inclusionCommaMap (F : X ⟶ Y) {x x' : X.total} (f : x ⟶ x') :
    inclusionCommaObj F x ⟶ inclusionCommaObj F x' where
  left := (toFunctor F).map f
  right := f
  w := inclusionCommaMap_comm F f

/-- The identity-arrow comma assignment preserves identities. -/
private theorem inclusionCommaMap_id (F : X ⟶ Y) (x : X.total) :
    inclusionCommaMap F (𝟙 x) = 𝟙 (inclusionCommaObj F x) := sorry
/- Proof strategy: apply `Comma.hom_ext`; the two component equalities are the identity laws for
`toFunctor F` and for `X.total`. -/

/-- The identity-arrow comma assignment preserves composition. -/
private theorem inclusionCommaMap_comp (F : X ⟶ Y) {x y z : X.total}
    (f : x ⟶ y) (g : y ⟶ z) :
    inclusionCommaMap F (f ≫ g) = inclusionCommaMap F f ≫ inclusionCommaMap F g := sorry
/- Proof strategy: apply `Comma.hom_ext`; the left component is `Functor.map_comp` for
`toFunctor F`, and the right component is reflexive. -/

/-- The identity-arrow embedding into the ambient comma category. -/
private def inclusionCommaFunctor (F : X ⟶ Y) :
    X.total ⥤ Comma (𝟭 Y.total) (toFunctor F) where
  obj := inclusionCommaObj F
  map := inclusionCommaMap F
  map_id := inclusionCommaMap_id F
  map_comp := inclusionCommaMap_comp F

/-- Every identity comparison object satisfies the verticality predicate. -/
private theorem inclusionCommaObj_mem (F : X ⟶ Y) (x : X.total) :
    verticalArrowProperty F ((inclusionCommaFunctor F).obj x) := sorry
/- Proof strategy: unfold `verticalArrowProperty`, `inclusionCommaFunctor`, and
`inclusionCommaObj`; apply `IsHomLift.id` to the base-object equality supplied by
`BasedFunctor.w_obj (toBasedFunctor F) x`. -/

end Implementation

/-- The identity-arrow embedding `X.total ⥤ VerticalComma F`. -/
private def inclusionFunctor (F : X ⟶ Y) : X.total ⥤ VerticalComma F :=
  (verticalArrowProperty F).lift (Implementation.inclusionCommaFunctor F)
    (Implementation.inclusionCommaObj_mem F)

/-- The identity-arrow embedding is a functor over `C`. -/
private theorem inclusionFunctorComm (F : X ⟶ Y) :
    inclusionFunctor F ⋙ projection F = X.p := sorry
/- Proof strategy: apply `Functor.ext`. The object part is `BasedFunctor.w_obj`; the map part is
`congr_hom (comm F)`. The full-subcategory lift and comma projections are definitionally the
identity-arrow components. -/

/-- The identity-arrow embedding preserves strongly cartesian arrows. -/
private theorem inclusionPreservesStronglyCartesian (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      ({ toFunctor := inclusionFunctor F
         w := inclusionFunctorComm F } :
        X.toBasedCategory ⥤ᵇ (middle F).toBasedCategory) := sorry
/- Proof strategy: the two components of `inclusionFunctor F` are `(toFunctor F).map φ` and
`φ`. The second is strongly cartesian by hypothesis and the first by
`FiberedCategoryOver.mapStronglyCartesian`; the componentwise comma universal property then
gives strong cartesianness for the lifted comma morphism. -/

/-- The fully faithful identity-arrow embedding `X ⟶ middle F`. -/
def inclusion (F : X ⟶ Y) : X ⟶ middle F :=
  ofBasedFunctor
    ({ toFunctor := inclusionFunctor F
       w := inclusionFunctorComm F } :
      X.toBasedCategory ⥤ᵇ (middle F).toBasedCategory)
    (inclusionPreservesStronglyCartesian F)

/-- The target-side endpoint of an identity-comparison object is `F(x)`. -/
@[simp]
theorem inclusion_obj_left (F : X ⟶ Y) (x : X.total) :
    ((toFunctor (inclusion F)).obj x).obj.left = (toFunctor F).obj x := sorry
/- Proof strategy: unfold `inclusion`; the full-subcategory lift stores the identity comma object,
whose left endpoint is `(toFunctor F).obj x`. -/

/-- The source-side endpoint of an identity-comparison object is `x`. -/
@[simp]
theorem inclusion_obj_right (F : X ⟶ Y) (x : X.total) :
    ((toFunctor (inclusion F)).obj x).obj.right = x := sorry
/- Proof strategy: unfold `inclusion`; the full-subcategory lift stores the identity comma object,
whose right endpoint is `x`. -/

/-- The comparison arrow of an object in the identity-arrow embedding is the identity. -/
@[simp]
theorem inclusion_obj_comparison (F : X ⟶ Y) (x : X.total) :
    ((toFunctor (inclusion F)).obj x).obj.hom = 𝟙 ((toFunctor F).obj x) := sorry
/- Proof strategy: unfold `inclusion`; the comparison field of the stored comma object was chosen
to be the identity of `(toFunctor F).obj x`. -/

/-- The left component of an embedded morphism is its image under `F`. -/
@[simp]
theorem inclusion_map_left (F : X ⟶ Y) {x y : X.total} (φ : x ⟶ y) :
    ((toFunctor (inclusion F)).map φ).hom.left = (toFunctor F).map φ := sorry
/- Proof strategy: unfold `inclusion`; the lifted comma morphism stores `(toFunctor F).map φ` as
its left component. -/

/-- The right component of an embedded morphism is the original morphism. -/
@[simp]
theorem inclusion_map_right (F : X ⟶ Y) {x y : X.total} (φ : x ⟶ y) :
    ((toFunctor (inclusion F)).map φ).hom.right = φ := sorry
/- Proof strategy: unfold `inclusion`; the lifted comma morphism stores `φ` as its right
component. -/

namespace Implementation

/-- Recover a source morphism from a morphism between identity-comparison objects. -/
private def inclusionPreimage (F : X ⟶ Y) {x y : X.total}
    (f : (toFunctor (inclusion F)).obj x ⟶ (toFunctor (inclusion F)).obj y) : x ⟶ y :=
  f.hom.right

/-- Mapping the recovered source morphism returns the original comma morphism. -/
private theorem inclusion_map_preimage (F : X ⟶ Y) {x y : X.total}
    (f : (toFunctor (inclusion F)).obj x ⟶ (toFunctor (inclusion F)).obj y) :
    (toFunctor (inclusion F)).map (inclusionPreimage F f) = f := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext` and then `Comma.hom_ext`. The right component is
reflexive; the comma-square equation for `f` identifies its left component with
`(toFunctor F).map f.hom.right` because both comparison arrows are identities. -/

/-- Recovering a morphism after applying the identity-arrow embedding is the identity. -/
private theorem inclusion_preimage_map (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    inclusionPreimage F ((toFunctor (inclusion F)).map f) = f := sorry
/- Proof strategy: unfold `inclusionPreimage`, `inclusion`, `inclusionFunctor`, and
`Implementation.inclusionCommaMap`; the right component of the lifted comma morphism is `f`
definitionally. -/

end Implementation

/-- The explicit fully-faithful structure on the identity-arrow embedding. -/
def inclusionFullyFaithful (F : X ⟶ Y) :
    (toFunctor (inclusion F)).FullyFaithful where
  preimage := Implementation.inclusionPreimage F
  map_preimage := Implementation.inclusion_map_preimage F
  preimage_map := Implementation.inclusion_preimage_map F

/-- Projecting an identity-comparison object back to its source is the identity morphism of `X`. -/
@[simp]
theorem inclusion_comp_toSource (F : X ⟶ Y) :
    inclusion F ≫ toSource F = 𝟙 X := sorry
/- Proof strategy: use extensionality for morphisms of fibred categories. The object and map
components reduce respectively to `inclusion_obj_right` and `inclusion_map_right`. -/

/-- The canonical legs recover `F`. -/
@[simp]
theorem inclusion_comp_toTarget (F : X ⟶ Y) :
    inclusion F ≫ toTarget F = F := sorry
/- Proof strategy: use extensionality for morphisms in the locally induced bicategory. After
forgetting to based functors, both object maps are `x ↦ F(x)` and both arrow maps are
`f ↦ F(f)` by `inclusion_obj_left` and `inclusion_map_left`. -/

end AdjointFactorization

end

end CategoryTheory.FiberedCategoryOver
