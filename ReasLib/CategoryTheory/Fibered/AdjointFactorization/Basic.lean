/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- Import decisions:
-- * `Comma.Basic` and `CategoryOver` own the exported vertical-comma carrier and
--   fibred-category construction.
public import Mathlib.CategoryTheory.Comma.Basic
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber

/-!
# Basic construction for adjoint factorization

This leaf owns the vertical-comma carrier and the intermediate fibred category.
The two factorization legs, the identity-comparison inclusion, and its adjunction
are kept in sibling leaves.
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

/-
For `F : X ⟶ Y`, an object of the intermediate category is a vertical arrow
`y ⟶ F(x)` in `Y`. Thus the construction is the full subcategory of the comma
category `(𝟭 Y.total ↓ toFunctor F)` cut out by `IsHomLift` over an identity.
The full-subcategory presentation records the actual reusable carrier without
choosing an unrelated factorization package.
-/

/-- The vertical-arrow predicate on `(𝟭 Y.total ↓ toFunctor F)`. -/
def verticalArrowProperty
    (F : X ⟶ Y) : ObjectProperty (Comma (𝟭 Y.total) (toFunctor F)) :=
  fun P ↦ Y.p.IsHomLift (𝟙 (Y.p.obj P.left)) P.hom

/-- The reducible carrier of vertical arrows `y ⟶ F(x)` used as the intermediate total category.
It remains an `abbrev` so the canonical full-subcategory `Category` instance is available without
introducing a second instance owner. -/
abbrev VerticalComma (F : X ⟶ Y) :=
  (verticalArrowProperty F).FullSubcategory

/-- The projection from `VerticalComma F` to the common base. -/
def projection (F : X ⟶ Y) : VerticalComma F ⥤ C :=
  (verticalArrowProperty F).ι ⋙ Comma.fst _ _ ⋙ Y.p

/-- The base of a vertical comma object is the base of its left endpoint. -/
@[simp]
theorem projection_obj (F : X ⟶ Y) (P : VerticalComma F) :
    (projection F).obj P = Y.p.obj P.obj.left := sorry
/- Proof strategy: unfold `projection`; then use `ObjectProperty.ι_obj` and the object formulas
for functor composition and `Comma.fst`. -/

/-- The projection of a vertical comma morphism is the projection of its left component. -/
@[simp]
theorem projection_map (F : X ⟶ Y) {P Q : VerticalComma F} (φ : P ⟶ Q) :
    (projection F).map φ = Y.p.map φ.hom.left := sorry
/- Proof strategy: unfold `projection`; then use `ObjectProperty.ι_map` and the map formulas for
functor composition and `Comma.fst`. -/

/-- The projection `VerticalComma F ⥤ C` is fibred. -/
@[instance]
theorem projectionIsFibered (F : X ⟶ Y) : (projection F).IsFibered := sorry
/- Proof strategy: given a base arrow into a vertical comma object, take the chosen cartesian
lifts of both endpoints. Lift the vertical comparison arrow through the source lift, package the
resulting comma square with `ObjectProperty.homMk`, and prove it strongly cartesian componentwise.
Then apply `Functor.IsFibered.of_exists_isStronglyCartesian`. -/

/-- The intermediate fibred category in the adjoint factorization of `F`. -/
def middle (F : X ⟶ Y) : FiberedCategoryOver C :=
  FiberedCategoryOver.ofFunctor (projection F)

end AdjointFactorization

end

end CategoryTheory.FiberedCategoryOver
