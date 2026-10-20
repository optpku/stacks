module

public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08Q4

# Pointwise products in functor categories

This file supplies fixed-family and binary product instances in functor categories, together with
the stable comparison isomorphisms relating evaluation to the corresponding products of values.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v v' u u'

namespace CategoryTheory.Limits.FunctorCategory

variable {K : Type u} [Category.{v} K]
variable {C : Type u'} [Category.{v'} C]

section Product

variable {T : Type w} (F : T → K ⥤ C)

/-- `HasPointwiseProduct F` records only the products of the particular evaluated families
`fun t ↦ (F t).obj k`.  It is the fixed-diagram alternative to requiring every `T`-indexed
product in `C`. -/
@[stacks 08Q4 "pointwise existence of a product of functors"]
class HasPointwiseProduct : Prop where
  /-- Every evaluated family has its required product. -/
  hasProduct (k : K) : HasProduct (fun t ↦ (F t).obj k)

attribute [instance] HasPointwiseProduct.hasProduct

namespace HasPointwiseProduct

/-- Products of the given shape in the target category supply pointwise products for every
family of functors. -/
@[stacks 08Q4 "pointwise products from products"]
instance ofProducts [HasProductsOfShape T C] : HasPointwiseProduct F where
  hasProduct _ := inferInstance

end HasPointwiseProduct

/-- A pointwise product supplies the product in the exact form requested by an evaluation
functor. -/
@[stacks 08Q4 "evaluated family product"]
instance (priority := low) pointwise.pi.hasProduct [HasPointwiseProduct F] (k : K) :
    HasProduct (fun t ↦ ((evaluation K C).obj k).obj (F t)) :=
  (inferInstance : HasPointwiseProduct F).hasProduct k

/-- A pointwise product hypothesis supplies the evaluated discrete limit used to construct the
product in the functor category. -/
@[stacks 08Q4 "evaluated product diagram"]
noncomputable instance (priority := low) pointwise.pi.hasLimit
    [HasPointwiseProduct F] (k : K) :
    HasLimit ((Discrete.functor F).flip.obj k) :=
  hasLimit_of_iso
    (Discrete.natIso (fun t => Iso.refl ((F t.as).obj k)) :
      Discrete.functor (fun t => (F t).obj k) ≅
        (Discrete.functor F).flip.obj k)

/-- Objectwise products of a fixed family give its product in the functor category. -/
@[stacks 08Q4 "pointwise product of functors"]
public noncomputable abbrev pointwise.product
    (F : T → K ⥤ C) [HasPointwiseProduct F] : HasProduct F :=
  functorCategoryHasLimit (Discrete.functor F)

/-- Evaluation identifies a product of a fixed family of functors with the corresponding product
of its values, without assuming that the target category has every product of this shape. -/
@[stacks 08Q4 "evaluation of a pointwise product"]
noncomputable def evaluation.piIso [HasPointwiseProduct F] (k : K) :
    (∏ᶜ F).obj k ≅ ∏ᶜ (fun t ↦ (F t).obj k) :=
  evaluation.limitIso (Discrete.functor F) k ≪≫
    HasLimit.isoOfNatIso
      (Discrete.compNatIsoDiscrete F ((evaluation K C).obj k))

/-- The comparison `evaluation.piIso` commutes with every product projection. -/
@[reassoc (attr := simp), stacks 08Q4 "evaluation of a product projection"]
theorem evaluation.piIso.hom_π [HasPointwiseProduct F] (k : K) (t : T) :
    (evaluation.piIso F k).hom ≫ Pi.π (fun t ↦ (F t).obj k) t =
      (Pi.π F t).app k := sorry

/-- The inverse comparison `evaluation.piIso` commutes with every product projection. -/
@[reassoc (attr := simp), stacks 08Q4 "inverse evaluation of a product projection"]
theorem evaluation.piIso.inv_π [HasPointwiseProduct F] (k : K) (t : T) :
    (evaluation.piIso F k).inv ≫ (Pi.π F t).app k =
      Pi.π (fun t ↦ (F t).obj k) t := sorry

/-- Under the evaluation comparisons, the structure map of a product of functors is the
product of the component structure maps. -/
@[reassoc, stacks 08Q4 "pointwise product structure map"]
theorem evaluation.piIso.map [HasPointwiseProduct F] {k l : K} (h : k ⟶ l) :
    (∏ᶜ F).map h ≫ (evaluation.piIso F l).hom =
      (evaluation.piIso F k).hom ≫ Pi.map (fun t ↦ (F t).map h) := sorry

/-- The inverse fixed-family product comparisons are natural in the evaluation object. -/
@[reassoc, stacks 08Q4 "inverse pointwise product structure map"]
theorem evaluation.piIso.inv_map [HasPointwiseProduct F] {k l : K} (h : k ⟶ l) :
    (evaluation.piIso F k).inv ≫ (∏ᶜ F).map h =
      Pi.map (fun t ↦ (F t).map h) ≫ (evaluation.piIso F l).inv := sorry

end Product

section BinaryProduct

variable (X Y : K ⥤ C)

namespace Binary

/-- `Binary.HasPointwiseProduct X Y` records binary products of `X.obj k` and `Y.obj k` at
every object `k`, without requiring unrelated binary products in `C`. -/
@[stacks 016Q "pointwise existence of a binary product of functors"]
class HasPointwiseProduct : Prop where
  /-- Every pair of evaluated objects has its required binary product. -/
  hasBinaryProduct (k : K) : HasBinaryProduct (X.obj k) (Y.obj k)

attribute [instance] HasPointwiseProduct.hasBinaryProduct

namespace HasPointwiseProduct

/-- Binary products in the target category supply pointwise binary products for every pair of
functors. -/
@[stacks 016Q "pointwise binary products from binary products"]
instance ofBinaryProducts [HasBinaryProducts C] : HasPointwiseProduct X Y where
  hasBinaryProduct _ := inferInstance

end HasPointwiseProduct

end Binary

/-- A pointwise binary product supplies the binary product in the exact form requested by an
evaluation functor. -/
@[stacks 016Q "evaluated pair product"]
instance (priority := low) pointwise.pair.hasBinaryProduct
    [Binary.HasPointwiseProduct X Y] (k : K) :
    HasBinaryProduct (((evaluation K C).obj k).obj X)
      (((evaluation K C).obj k).obj Y) :=
  (inferInstance : Binary.HasPointwiseProduct X Y).hasBinaryProduct k

/-- The evaluated pair diagram has a limit whenever its two values have a binary product. -/
@[stacks 016Q "objectwise pair limit"]
noncomputable instance (priority := low) pointwise.pair.hasLimit
    [Binary.HasPointwiseProduct X Y] (k : K) :
    HasLimit ((pair X Y).flip.obj k) :=
  hasLimit_of_iso (pairComp X Y ((evaluation K C).obj k)).symm

/-- Objectwise binary products give the binary product in the functor category. -/
@[stacks 016Q "pointwise binary product of functors"]
public noncomputable abbrev pointwise.binaryProduct
    (X Y : K ⥤ C) [Binary.HasPointwiseProduct X Y] :
    HasBinaryProduct X Y :=
  functorCategoryHasLimit (pair X Y)

/-- Evaluation identifies a functor-category binary product with the corresponding objectwise
product.  This is the generic comparison used by both the pointwise-product and binary-product
facades. -/
@[stacks 016Q "pointwise binary-product comparison", stacks 016Z]
noncomputable def evaluation.productIso
    [Binary.HasPointwiseProduct X Y] (k : K) :
    (X ⨯ Y).obj k ≅ X.obj k ⨯ Y.obj k :=
  evaluation.limitIso (pair X Y) k ≪≫
    HasLimit.isoOfNatIso (pairComp X Y ((evaluation K C).obj k))

/-- The first projection of `evaluation.productIso` is the evaluated first projection. -/
@[reassoc (attr := simp), stacks 016Q "pointwise first projection", stacks 016Z]
theorem evaluation.productIso.fst
    [Binary.HasPointwiseProduct X Y] (k : K) :
    (evaluation.productIso X Y k).hom ≫ prod.fst = (prod.fst : X ⨯ Y ⟶ X).app k := sorry

/-- The second projection of `evaluation.productIso` is the evaluated second projection. -/
@[reassoc (attr := simp), stacks 016Q "pointwise second projection", stacks 016Z]
theorem evaluation.productIso.snd
    [Binary.HasPointwiseProduct X Y] (k : K) :
    (evaluation.productIso X Y k).hom ≫ prod.snd = (prod.snd : X ⨯ Y ⟶ Y).app k := sorry

/-- The inverse comparison carries the evaluated first projection back to the pointwise first
projection. -/
@[reassoc (attr := simp), stacks 016Q "inverse pointwise first projection", stacks 016Z]
theorem evaluation.productIso.inv_fst
    [Binary.HasPointwiseProduct X Y] (k : K) :
    (evaluation.productIso X Y k).inv ≫ (prod.fst : X ⨯ Y ⟶ X).app k =
      prod.fst := sorry

/-- The inverse comparison carries the evaluated second projection back to the pointwise second
projection. -/
@[reassoc (attr := simp), stacks 016Q "inverse pointwise second projection", stacks 016Z]
theorem evaluation.productIso.inv_snd
    [Binary.HasPointwiseProduct X Y] (k : K) :
    (evaluation.productIso X Y k).inv ≫ (prod.snd : X ⨯ Y ⟶ Y).app k =
      prod.snd := sorry

/-- Under the evaluation comparisons, the structure map of a binary product of functors is the
binary product of the two structure maps. -/
@[reassoc, stacks 016Q "pointwise binary-product structure map", stacks 016Z]
theorem evaluation.productIso.map
    [Binary.HasPointwiseProduct X Y] {k l : K} (h : k ⟶ l) :
    (X ⨯ Y).map h ≫ (evaluation.productIso X Y l).hom =
      (evaluation.productIso X Y k).hom ≫ prod.map (X.map h) (Y.map h) := sorry

/-- The inverse binary-product comparisons are natural in the evaluation object. -/
@[reassoc, stacks 016Q "inverse pointwise binary-product structure map", stacks 016Z]
theorem evaluation.productIso.inv_map
    [Binary.HasPointwiseProduct X Y] {k l : K} (h : k ⟶ l) :
    (evaluation.productIso X Y k).inv ≫ (X ⨯ Y).map h =
      prod.map (X.map h) (Y.map h) ≫ (evaluation.productIso X Y l).inv := sorry

end BinaryProduct

end CategoryTheory.Limits.FunctorCategory
