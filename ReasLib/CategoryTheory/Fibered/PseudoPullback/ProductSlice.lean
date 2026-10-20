/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Product-slice functor for explicit pseudo-pullbacks

This leaf owns the base-level construction sending an explicit pseudo-pullback
of slice-based categories to the slice over the binary product.  It is stated
for arbitrary based categories: neither fibred-in-groupoids hypotheses nor
relative-representability data are needed for the construction.

The groupoid-specific `TwoFibreProduct.toProductSlice` bridge lives in the
two-fibre-product hierarchy and imports this neutral owner.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory

variable {C : Type u} [Category.{v} C]

section PseudoPullbackProductSlice

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable [Limits.HasBinaryProducts C]
variable {U V : C}
variable {S : BasedCategory C}
variable (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ S)
variable (G : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ S)

namespace BasedCategory.PseudoPullback.ProductSlice

namespace Implementation

omit [Limits.HasBinaryProducts C] in
/-- The `U`-slice component of a morphism in the explicit pseudo-pullback is compatible with
its stored base arrow. -/
private theorem fstBaseComp
    {P Q : (BasedCategory.PseudoPullback F G).obj} (φ : P ⟶ Q) :
    BasedCategory.PseudoPullback.baseMap φ ≫
        ((BasedCategory.PseudoPullback.fstBaseIso Q).inv ≫
          (BasedCategory.PseudoPullback.fiberObj Q).fst.1.hom) =
      (BasedCategory.PseudoPullback.fstBaseIso P).inv ≫
        (BasedCategory.PseudoPullback.fiberObj P).fst.1.hom := sorry
/- Proof strategy: eliminate the stored object equalities, identify `φ.base` with the underlying
arrow of `φ.a` via `IsHomLift.eq_of_isHomLift`, and apply `Over.w φ.a`. -/

omit [Limits.HasBinaryProducts C] in
/-- The `V`-slice component of a morphism in the explicit pseudo-pullback is compatible with
its stored base arrow. -/
private theorem sndBaseComp
    {P Q : (BasedCategory.PseudoPullback F G).obj} (φ : P ⟶ Q) :
    BasedCategory.PseudoPullback.baseMap φ ≫
        ((BasedCategory.PseudoPullback.sndBaseIso Q).inv ≫
          (BasedCategory.PseudoPullback.fiberObj Q).snd.1.hom) =
      (BasedCategory.PseudoPullback.sndBaseIso P).inv ≫
        (BasedCategory.PseudoPullback.fiberObj P).snd.1.hom := sorry
/- Proof strategy: eliminate the stored object equalities, identify `φ.base` with the underlying
arrow of `φ.b` via `IsHomLift.eq_of_isHomLift`, and apply `Over.w φ.b`. -/

/-- The product-slice object associated to an object of the explicit pseudo-pullback. -/
private noncomputable def object
    (P : (BasedCategory.PseudoPullback F G).obj) : Over (Limits.prod U V) :=
  Over.mk (Limits.prod.lift
    ((BasedCategory.PseudoPullback.fstBaseIso P).inv ≫
      (BasedCategory.PseudoPullback.fiberObj P).fst.1.hom)
    ((BasedCategory.PseudoPullback.sndBaseIso P).inv ≫
      (BasedCategory.PseudoPullback.fiberObj P).snd.1.hom))

/-- Compatibility of a stored base morphism with the induced product-slice arrows. -/
private theorem map_comm
    {P Q : (BasedCategory.PseudoPullback F G).obj} (φ : P ⟶ Q) :
    BasedCategory.PseudoPullback.baseMap φ ≫
        (object (U := U) (V := V) (S := S) F G Q).hom =
      (object (U := U) (V := V) (S := S) F G P).hom := sorry
/- Proof strategy: apply `Limits.prod.hom_ext`; the projection equations are `fstBaseComp` and
`sndBaseComp`. -/

/-- The product-slice morphism induced by a morphism of the explicit pseudo-pullback. -/
private noncomputable def map
    {P Q : (BasedCategory.PseudoPullback F G).obj} (φ : P ⟶ Q) :
    object (U := U) (V := V) (S := S) F G P ⟶ object (U := U) (V := V) (S := S) F G Q :=
  Over.homMk (BasedCategory.PseudoPullback.baseMap φ)
    (map_comm (U := U) (V := V) (S := S) F G φ)

/-- The product-slice map preserves identities. -/
private theorem map_id
    (P : (BasedCategory.PseudoPullback F G).obj) :
    map (U := U) (V := V) (S := S) F G (𝟙 P) =
      𝟙 (object (U := U) (V := V) (S := S) F G P) := sorry
/- Proof strategy: apply `Over.OverMorphism.ext`; the underlying morphism is an identity. -/

/-- The product-slice map preserves composition. -/
private theorem map_comp
    {P Q R : (BasedCategory.PseudoPullback F G).obj}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    map (U := U) (V := V) (S := S) F G (φ ≫ ψ) =
      map (U := U) (V := V) (S := S) F G φ ≫ map (U := U) (V := V) (S := S) F G ψ := sorry
/- Proof strategy: apply `Over.OverMorphism.ext`; both sides have underlying arrow
`φ.base ≫ ψ.base`. -/

end Implementation

/-- The explicit pseudo-pullback of two slice-based functors maps canonically to the product
slice: an object over `T` with arrows `T ⟶ U` and `T ⟶ V` is sent to `T ⟶ U × V`. -/
@[stacks 0040 "product-slice functor for an explicit pseudo-pullback"]
noncomputable def toProduct :
    (BasedCategory.PseudoPullback F G).obj ⥤ Over (Limits.prod U V) where
  obj P := Implementation.object (U := U) (V := V) (S := S) F G P
  map φ := Implementation.map (U := U) (V := V) (S := S) F G φ
  map_id := Implementation.map_id (U := U) (V := V) (S := S) F G
  map_comp := Implementation.map_comp (U := U) (V := V) (S := S) F G

/-- The product-slice functor retains the common base object as the domain of the resulting
slice arrow. -/
@[simp]
theorem toProduct.obj.left (P : (BasedCategory.PseudoPullback F G).obj) :
    (toProduct (U := U) (V := V) (S := S) F G |>.obj P).left =
      BasedCategory.PseudoPullback.baseObj P := sorry

/-- The first product projection of the product-slice arrow is the transported `U`-slice
component of the explicit pseudo-pullback object. -/
@[simp]
theorem toProduct.obj.hom.fst (P : (BasedCategory.PseudoPullback F G).obj) :
    (toProduct (U := U) (V := V) (S := S) F G |>.obj P).hom ≫ Limits.prod.fst =
      (BasedCategory.PseudoPullback.fstBaseIso P).inv ≫
        (BasedCategory.PseudoPullback.fiberObj P).fst.1.hom := sorry

/-- The second product projection of the product-slice arrow is the transported `V`-slice
component of the explicit pseudo-pullback object. -/
@[simp]
theorem toProduct.obj.hom.snd (P : (BasedCategory.PseudoPullback F G).obj) :
    (toProduct (U := U) (V := V) (S := S) F G |>.obj P).hom ≫ Limits.prod.snd =
      (BasedCategory.PseudoPullback.sndBaseIso P).inv ≫
        (BasedCategory.PseudoPullback.fiberObj P).snd.1.hom := sorry

/-- On morphisms, the product-slice functor retains the common base map as the underlying slice
map. -/
@[simp]
theorem toProduct.map.left
    {P Q : (BasedCategory.PseudoPullback F G).obj} (φ : P ⟶ Q) :
    (toProduct (U := U) (V := V) (S := S) F G |>.map φ).left =
      BasedCategory.PseudoPullback.baseMap φ := sorry

/-- Forgetting `toProduct` recovers the base projection of the explicit pseudo-pullback
strictly. -/
@[simp]
theorem toProduct.comp_forget :
    toProduct (U := U) (V := V) (S := S) F G ⋙ Over.forget (Limits.prod U V) =
      (BasedCategory.PseudoPullback F G).p := sorry
/- Proof strategy: apply `Functor.ext`; object and morphism components are definitionally the
stored base object and base arrow. -/

/-- The product-slice construction as a morphism in the category of categories over `C`.

This is the bundled consumer API for `toProduct`: it retains the strict projection equation, so it
can be composed and passed to constructions formulated in `BasedCategory` without repeatedly
rebuilding `BasedFunctor.ofFunctor` at each use site. -/
@[stacks 0040 "based product-slice functor for an explicit pseudo-pullback"]
noncomputable def toProduct.basedFunctor :
    BasedCategory.PseudoPullback F G ⥤ᵇ
      BasedCategory.ofFunctor (Over.forget (Limits.prod U V)) :=
  { toFunctor := toProduct (U := U) (V := V) (S := S) F G
    w := toProduct.comp_forget (U := U) (V := V) (S := S) F G }

/-- The underlying functor of `toProduct.basedFunctor` is the explicit product-slice functor. -/
@[simp]
theorem toProduct.basedFunctor.toFunctor :
    (toProduct.basedFunctor (U := U) (V := V) (S := S) F G).toFunctor =
      toProduct (U := U) (V := V) (S := S) F G := sorry

/-- The bundled product-slice functor is strictly over the common base. -/
@[simp]
theorem toProduct.basedFunctor.comp_forget :
    (toProduct.basedFunctor (U := U) (V := V) (S := S) F G).toFunctor ⋙
        Over.forget (Limits.prod U V) =
      (BasedCategory.PseudoPullback F G).p := sorry

end BasedCategory.PseudoPullback.ProductSlice

end PseudoPullbackProductSlice

end CategoryTheory
