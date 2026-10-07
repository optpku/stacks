module

public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise coproducts in functor categories

This file supplies fixed-family and binary coproduct instances in functor categories, together
with the stable comparison isomorphisms relating evaluation to the corresponding coproducts of
values.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v v' u u'

namespace CategoryTheory.Limits.FunctorCategory

variable {K : Type u} [Category.{v} K]
variable {C : Type u'} [Category.{v'} C]

section Coproduct

variable {T : Type w} (F : T → K ⥤ C)

/-- `HasPointwiseCoproduct F` records only the coproducts of the particular evaluated families
`fun t ↦ (F t).obj k`. It is the fixed-diagram alternative to requiring every `T`-indexed
coproduct in `C`. -/
@[stacks 016W "pointwise existence of a coproduct of functors"]
class HasPointwiseCoproduct : Prop where
  /-- Every evaluated family has its required coproduct. -/
  hasCoproduct (k : K) : HasCoproduct (fun t ↦ (F t).obj k)

attribute [instance] HasPointwiseCoproduct.hasCoproduct

namespace HasPointwiseCoproduct

/-- Coproducts of the given shape in the target category supply pointwise coproducts for every
family of functors. -/
@[stacks 016W "pointwise coproducts from coproducts"]
instance ofCoproducts [HasCoproductsOfShape T C] : HasPointwiseCoproduct F := sorry

end HasPointwiseCoproduct

/-- A pointwise coproduct supplies the coproduct in the exact form requested by an evaluation
functor. -/
@[stacks 016W "evaluated family coproduct"]
instance (priority := low) pointwise.sigma.hasCoproduct [HasPointwiseCoproduct F] (k : K) :
    HasCoproduct (fun t ↦ ((evaluation K C).obj k).obj (F t)) :=
  (inferInstance : HasPointwiseCoproduct F).hasCoproduct k

/-- A pointwise coproduct hypothesis supplies the evaluated discrete colimit used to construct
the coproduct in the functor category. -/
@[stacks 016W "evaluated coproduct diagram"]
noncomputable instance (priority := low) pointwise.sigma.hasColimit
    [HasPointwiseCoproduct F] (k : K) :
    HasColimit ((Discrete.functor F).flip.obj k) :=
  hasColimit_of_iso
    (Discrete.natIso (fun t ↦ Iso.refl ((F t.as).obj k)) :
      Discrete.functor (fun t ↦ (F t).obj k) ≅
        (Discrete.functor F).flip.obj k).symm

/-- Objectwise coproducts give the canonical coproduct of a fixed family of functors. -/
@[stacks 016W "pointwise coproduct of functors"]
public noncomputable abbrev pointwise.coproduct (F : T → K ⥤ C)
    [HasPointwiseCoproduct F] :
    HasCoproduct F :=
  functorCategoryHasColimit (Discrete.functor F)

/-- Evaluation identifies a coproduct of a fixed family of functors with the corresponding
coproduct of its values, without assuming that the target category has every coproduct of this
shape. -/
@[stacks 016W "evaluation of a pointwise coproduct"]
noncomputable def evaluation.sigmaIso [HasPointwiseCoproduct F] (k : K) :
    (∐ F).obj k ≅ ∐ fun t ↦ (F t).obj k :=
  evaluation.colimitIso (Discrete.functor F) k ≪≫
    HasColimit.isoOfNatIso
      (Discrete.compNatIsoDiscrete F ((evaluation K C).obj k))

/-- The comparison `evaluation.sigmaIso` commutes with every coproduct inclusion. -/
@[reassoc (attr := simp), stacks 016W "evaluation of a coproduct inclusion"]
theorem evaluation.sigmaIso.ι_hom [HasPointwiseCoproduct F] (k : K) (t : T) :
    (Sigma.ι F t).app k ≫ (evaluation.sigmaIso F k).hom =
      Sigma.ι (fun t ↦ (F t).obj k) t := sorry

/-- The inverse comparison `evaluation.sigmaIso` commutes with every coproduct inclusion. -/
@[reassoc (attr := simp), stacks 016W "inverse evaluation of a coproduct inclusion"]
theorem evaluation.sigmaIso.ι_inv [HasPointwiseCoproduct F] (k : K) (t : T) :
    Sigma.ι (fun t ↦ (F t).obj k) t ≫ (evaluation.sigmaIso F k).inv =
      (Sigma.ι F t).app k := sorry

/-- Under the evaluation comparisons, the structure map of a coproduct of functors is the
coproduct of the component structure maps. -/
@[reassoc, stacks 016W "pointwise coproduct structure map"]
theorem evaluation.sigmaIso.map [HasPointwiseCoproduct F] {k l : K} (h : k ⟶ l) :
    (∐ F).map h ≫ (evaluation.sigmaIso F l).hom =
      (evaluation.sigmaIso F k).hom ≫ Sigma.map (fun t ↦ (F t).map h) := sorry

/-- The inverse fixed-family coproduct comparisons are natural in the evaluation object. -/
@[reassoc, stacks 016W "inverse pointwise coproduct structure map"]
theorem evaluation.sigmaIso.inv_map [HasPointwiseCoproduct F] {k l : K} (h : k ⟶ l) :
    (evaluation.sigmaIso F k).inv ≫ (∐ F).map h =
      Sigma.map (fun t ↦ (F t).map h) ≫ (evaluation.sigmaIso F l).inv := sorry

end Coproduct

section BinaryCoproduct

variable (X Y : K ⥤ C)

namespace Binary

/-- `Binary.HasPointwiseCoproduct X Y` records binary coproducts of `X.obj k` and `Y.obj k` at
every object `k`, without requiring unrelated binary coproducts in `C`. -/
@[stacks 016W "pointwise existence of a binary coproduct of functors"]
class HasPointwiseCoproduct : Prop where
  /-- Every pair of evaluated objects has its required binary coproduct. -/
  hasBinaryCoproduct (k : K) : HasBinaryCoproduct (X.obj k) (Y.obj k)

attribute [instance] HasPointwiseCoproduct.hasBinaryCoproduct

namespace HasPointwiseCoproduct

/-- Binary coproducts in the target category supply pointwise binary coproducts for every pair of
functors. -/
@[stacks 016W "pointwise binary coproducts from binary coproducts"]
instance ofBinaryCoproducts [HasBinaryCoproducts C] : HasPointwiseCoproduct X Y := sorry

end HasPointwiseCoproduct

end Binary

/-- A pointwise binary coproduct supplies the binary coproduct in the exact form requested by an
evaluation functor. -/
@[stacks 016W "evaluated pair coproduct"]
instance (priority := low) pointwise.pair.hasBinaryCoproduct
    [Binary.HasPointwiseCoproduct X Y] (k : K) :
    HasBinaryCoproduct (((evaluation K C).obj k).obj X)
      (((evaluation K C).obj k).obj Y) :=
  (inferInstance : Binary.HasPointwiseCoproduct X Y).hasBinaryCoproduct k

/-- The evaluated pair diagram has a colimit whenever its two values have a binary coproduct. -/
@[stacks 016W "objectwise pair colimit"]
noncomputable instance (priority := low) pointwise.pair.hasColimit
    [Binary.HasPointwiseCoproduct X Y] (k : K) :
    HasColimit ((pair X Y).flip.obj k) :=
  hasColimit_of_iso (pairComp X Y ((evaluation K C).obj k))

/-- Objectwise binary coproducts give the canonical binary coproduct in a functor category. -/
@[stacks 016W "objectwise binary coproduct"]
public noncomputable abbrev pointwise.binaryCoproduct (F G : K ⥤ C)
    [Binary.HasPointwiseCoproduct F G] :
    HasBinaryCoproduct F G :=
  functorCategoryHasColimit (pair F G)

/-- Evaluation identifies a functor-category binary coproduct with the corresponding objectwise
coproduct. -/
@[stacks 016W]
noncomputable def evaluation.coproductIso
    [Binary.HasPointwiseCoproduct X Y] (k : K) :
    (X ⨿ Y).obj k ≅ X.obj k ⨿ Y.obj k :=
  evaluation.colimitIso (pair X Y) k ≪≫
    HasColimit.isoOfNatIso (pairComp X Y ((evaluation K C).obj k))

/-- The first inclusion into `evaluation.coproductIso` is the evaluated first inclusion. -/
@[reassoc (attr := simp), stacks 016W]
theorem evaluation.coproductIso.inl
    [Binary.HasPointwiseCoproduct X Y] (k : K) :
    (coprod.inl : X ⟶ X ⨿ Y).app k ≫ (evaluation.coproductIso X Y k).hom =
      (coprod.inl : X.obj k ⟶ X.obj k ⨿ Y.obj k) := sorry

/-- The second inclusion into `evaluation.coproductIso` is the evaluated second inclusion. -/
@[reassoc (attr := simp), stacks 016W]
theorem evaluation.coproductIso.inr
    [Binary.HasPointwiseCoproduct X Y] (k : K) :
    (coprod.inr : Y ⟶ X ⨿ Y).app k ≫ (evaluation.coproductIso X Y k).hom =
      (coprod.inr : Y.obj k ⟶ X.obj k ⨿ Y.obj k) := sorry

/-- The inverse comparison carries the evaluated first inclusion back to the pointwise first
inclusion. -/
@[reassoc (attr := simp), stacks 016W "inverse pointwise coproduct first inclusion"]
theorem evaluation.coproductIso.inl_inv
    [Binary.HasPointwiseCoproduct X Y] (k : K) :
    (coprod.inl : X.obj k ⟶ X.obj k ⨿ Y.obj k) ≫ (evaluation.coproductIso X Y k).inv =
      (coprod.inl : X ⟶ X ⨿ Y).app k := sorry

/-- The inverse comparison carries the evaluated second inclusion back to the pointwise second
inclusion. -/
@[reassoc (attr := simp), stacks 016W "inverse pointwise coproduct second inclusion"]
theorem evaluation.coproductIso.inr_inv
    [Binary.HasPointwiseCoproduct X Y] (k : K) :
    (coprod.inr : Y.obj k ⟶ X.obj k ⨿ Y.obj k) ≫ (evaluation.coproductIso X Y k).inv =
      (coprod.inr : Y ⟶ X ⨿ Y).app k := sorry

/-- Under the evaluation comparisons, the structure map of a binary coproduct of functors is the
binary coproduct of the two structure maps. -/
@[reassoc, stacks 016W "pointwise binary-coproduct structure map"]
theorem evaluation.coproductIso.map
    [Binary.HasPointwiseCoproduct X Y] {k l : K} (h : k ⟶ l) :
    (X ⨿ Y).map h ≫ (evaluation.coproductIso X Y l).hom =
      (evaluation.coproductIso X Y k).hom ≫ coprod.map (X.map h) (Y.map h) := sorry

/-- The inverse binary-coproduct comparisons are natural in the evaluation object. -/
@[reassoc, stacks 016W "inverse pointwise binary-coproduct structure map"]
theorem evaluation.coproductIso.inv_map
    [Binary.HasPointwiseCoproduct X Y] {k l : K} (h : k ⟶ l) :
    (evaluation.coproductIso X Y k).inv ≫ (X ⨿ Y).map h =
      coprod.map (X.map h) (Y.map h) ≫ (evaluation.coproductIso X Y l).inv := sorry

end BinaryCoproduct

end CategoryTheory.Limits.FunctorCategory
