/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.Equivalence

@[expose] public section

/-!
# Product slices: computations

This module records the object, morphism, and unit/counit component formulas of the canonical
product-slice equivalence.  The deterministic functors live in `ProductSlice.Basic`, while the
equivalence owner lives in `ProductSlice.Equivalence`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

universe v u

namespace CategoryTheory

namespace Limits.CategoricalPullback.ProductSlice

section Computations

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- The forward product-slice functor keeps the common domain represented by the first slice
object. -/
@[simp] theorem toProduct.obj.left (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    ((toProduct U V).obj x).left = x.fst.left := sorry
/- Proof strategy: unfold only the public `toProduct` owner and read the domain of its `Over.mk` object. -/

/-- The arrow represented by the forward product-slice functor projects to the first slice
arrow. -/
@[simp] theorem toProduct.obj.hom.fst (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    ((toProduct U V).obj x).hom ≫ Limits.prod.fst = x.fst.hom := sorry
/- Proof strategy: expose the product lift stored by `toProduct` and apply
`Limits.prod.lift_fst`. -/

/-- The arrow represented by the forward product-slice functor projects to the transported
second slice arrow. -/
@[simp] theorem toProduct.obj.hom.snd (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    ((toProduct U V).obj x).hom ≫ Limits.prod.snd = x.iso.hom ≫ x.snd.hom := sorry
/- Proof strategy: expose the product lift stored by `toProduct` and apply
`Limits.prod.lift_snd`. -/

/-- On morphisms, the forward product-slice functor uses the underlying arrow of the first
slice component. -/
@[simp] theorem toProduct.map.left (U V : C)
    {x y : (Over.forget U) ⊡ (Over.forget V)} (f : x ⟶ y) :
    ((toProduct U V).map f).left = f.fst.left := sorry
/- Proof strategy: unfold the public functor owner and read the arrow supplied to `Over.homMk`. -/

/-- The first object projection of the inverse product-slice functor is the slice arrow obtained
by postcomposing with the first product projection. -/
@[simp] theorem fromProduct.obj.fst (U V : C) (c : Over (Limits.prod U V)) :
    ((fromProduct U V).obj c).fst = Over.mk (c.hom ≫ Limits.prod.fst) := sorry
/- Proof strategy: unfold only the public `fromProduct` owner and read its first object field. -/

/-- The second object projection of the inverse product-slice functor is the slice arrow obtained
by postcomposing with the second product projection. -/
@[simp] theorem fromProduct.obj.snd (U V : C) (c : Over (Limits.prod U V)) :
    ((fromProduct U V).obj c).snd = Over.mk (c.hom ≫ Limits.prod.snd) := sorry
/- Proof strategy: unfold only the public `fromProduct` owner and read its second object field. -/

/-- The structural comparison of an inverse product-slice object is the identity on its common
domain. -/
@[simp] theorem fromProduct.obj.iso (U V : C) (c : Over (Limits.prod U V)) :
    ((fromProduct U V).obj c).iso = Iso.refl c.left := sorry
/- Proof strategy: unfold the public inverse functor and read the identity isomorphism stored in
the categorical-pullback object. -/

/-- The forward structural comparison of an inverse product-slice object is the identity on its
common domain. -/
@[simp] theorem fromProduct.obj.iso.hom (U V : C) (c : Over (Limits.prod U V)) :
    ((fromProduct U V).obj c).iso.hom = 𝟙 c.left := sorry
/- Proof strategy: unfold the public inverse functor and read the identity isomorphism stored in
the categorical-pullback object. -/

/-- The inverse structural comparison of an inverse product-slice object is the identity on its
common domain. -/
@[simp] theorem fromProduct.obj.iso.inv (U V : C) (c : Over (Limits.prod U V)) :
    ((fromProduct U V).obj c).iso.inv = 𝟙 c.left := sorry
/- Proof strategy: rewrite with `fromProduct.obj.iso` and read the inverse of the identity
isomorphism. -/

/-- The first projected morphism of the inverse product-slice functor retains the underlying
slice arrow. -/
@[simp] theorem fromProduct.map.fst.left (U V : C)
    {c d : Over (Limits.prod U V)} (g : c ⟶ d) :
    (((fromProduct U V).map g).fst).left = g.left := sorry
/- Proof strategy: unfold the public inverse functor and read the first `Over.homMk` component. -/

/-- The second projected morphism of the inverse product-slice functor retains the underlying
slice arrow. -/
@[simp] theorem fromProduct.map.snd.left (U V : C)
    {c d : Over (Limits.prod U V)} (g : c ⟶ d) :
    (((fromProduct U V).map g).snd).left = g.left := sorry
/- Proof strategy: unfold the public inverse functor and read the second `Over.homMk` component. -/

/-- The forward functor of the canonical product-slice equivalence is `toProduct`. -/
@[simp] theorem equivalence.functor (U V : C) :
    (equivalence U V).functor = toProduct U V := sorry
/- Proof strategy: unfold the public equivalence owner and read its forward-functor field. -/

/-- The inverse functor of the canonical product-slice equivalence is `fromProduct`. -/
@[simp] theorem equivalence.inverse (U V : C) :
    (equivalence U V).inverse = fromProduct U V := sorry
/- Proof strategy: unfold the public equivalence owner and read its inverse-functor field. -/

/-- The first slice component of the forward unit map is the identity on the common domain. -/
@[simp]
theorem equivalence.unitIso.hom.app.fst (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    ((equivalence U V).unitIso.hom.app x).fst.left =
      𝟙 x.fst.left := sorry

/-- The second slice component of the forward unit map is the inverse of the pullback object's
structural isomorphism. -/
@[simp]
theorem equivalence.unitIso.hom.app.snd (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    ((equivalence U V).unitIso.hom.app x).snd.left =
      x.iso.inv := sorry

/-- The first slice component of the inverse unit map is the identity on the common domain. -/
@[simp]
theorem equivalence.unitIso.inv.app.fst (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    ((equivalence U V).unitIso.inv.app x).fst.left =
      𝟙 x.fst.left := sorry

/-- The second slice component of the inverse unit map is the pullback object's structural
isomorphism. -/
@[simp]
theorem equivalence.unitIso.inv.app.snd (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    ((equivalence U V).unitIso.inv.app x).snd.left =
      x.iso.hom := sorry

/-- The forward counit map is the identity on the underlying domain of the product-slice
object. -/
@[simp]
theorem equivalence.counitIso.hom.app.left (U V : C)
    (c : Over (Limits.prod U V)) :
    ((equivalence U V).counitIso.hom.app c).left =
      𝟙 c.left := sorry

/-- The inverse counit map is the identity on the underlying domain of the product-slice
object. -/
@[simp]
theorem equivalence.counitIso.inv.app.left (U V : C)
    (c : Over (Limits.prod U V)) :
    ((equivalence U V).counitIso.inv.app c).left =
      𝟙 c.left := sorry

end Computations

end Limits.CategoricalPullback.ProductSlice

end CategoryTheory
