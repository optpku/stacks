/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Concrete diagonal model for iterated categorical pullbacks

The explicit comparison from the direct diagonal model to the corresponding iterated
categorical-pullback model.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Prod
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe vC vS uC uS

namespace CategoryTheory.Limits

noncomputable section

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable (G₁ G₂ : C ⥤ S)

namespace CategoricalPullback.DiagonalModel

/-- The direct diagonal categorical-pullback model associated to `G₁` and `G₂`.

It is the categorical pullback of `G₁.prod' G₂` along `Functor.diag S`, namely the model
`C ×[(S × S)] S`. This transparent type vocabulary is shared by the concrete comparison and its
equivalence API. -/
abbrev direct :=
  CategoricalPullback (G₁.prod' G₂) (Functor.diag S)

/-- The iterated categorical-pullback model associated to `G₁` and `G₂`.

It is the categorical pullback of the two projections from `G₁ ⊡ G₂` along `Functor.diag C`,
namely `(G₁ ⊡ G₂) ×[(C × C)] C`. This transparent type vocabulary is shared by the concrete
comparison and its equivalence API. -/
abbrev iterated :=
  CategoricalPullback (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)) (Functor.diag C)

end CategoricalPullback.DiagonalModel

/- `CategoricalPullback.DiagonalModel.direct G₁ G₂` is `C ×[(S × S)] S`, while
`CategoricalPullback.DiagonalModel.iterated G₁ G₂` is the concrete model
`(G₁ ⊡ G₂) ×[(C × C)] C`. The construction below changes only the presentation of this
specified model; it does not use a bilimit hypothesis. -/

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace CategoricalPullback.DiagonalModel.Implementation

/-- The canonical square presenting the diagonal model `C ×[(S × S)] S`. -/
private def sourceSquare :
    CatCommSqOver (G₁.prod' G₂) (Functor.diag S)
      (CategoricalPullback.DiagonalModel.direct G₁ G₂) :=
  (toCatCommSqOver (G₁.prod' G₂) (Functor.diag S)
    (CategoricalPullback.DiagonalModel.direct G₁ G₂)).obj (𝟭 _)

/-- The square over `G₁` and `G₂` obtained by using the `C`-leg of the diagonal model twice. -/
private def firstSquare :
    CatCommSqOver G₁ G₂ (CategoricalPullback.DiagonalModel.direct G₁ G₂) :=
  let Q := sourceSquare G₁ G₂
  { fst := Q.fst
    snd := Q.fst
    iso :=
      (Functor.isoWhiskerLeft _ (Functor.prod'CompFst G₁ G₂).symm ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight Q.iso (CategoryTheory.Prod.fst S S) ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.prod'CompFst (𝟭 S) (𝟭 S)) ≪≫
          Functor.rightUnitor _) ≪≫
        (Functor.isoWhiskerLeft _ (Functor.prod'CompSnd G₁ G₂).symm ≪≫
            (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight Q.iso (CategoryTheory.Prod.snd S S) ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (Functor.prod'CompSnd (𝟭 S) (𝟭 S)) ≪≫
            Functor.rightUnitor _).symm }

/-- The canonical comparison from the diagonal model to the inner pullback `G₁ ⊡ G₂`. -/
private def firstComparison :
    CategoricalPullback.DiagonalModel.direct G₁ G₂ ⥤ G₁ ⊡ G₂ :=
  (firstSquare G₁ G₂).comparison

/-- Naturality of the identity components that place the diagonal model over the outer cospan. -/
private theorem iteratedIsoNaturality
    {X Y : CategoricalPullback.DiagonalModel.direct G₁ G₂} (f : X ⟶ Y) :
    (firstComparison G₁ G₂ ⋙
          Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂)).map f ≫
        𝟙 (((sourceSquare G₁ G₂).fst ⋙ Functor.diag C).obj Y) =
      𝟙 (((sourceSquare G₁ G₂).fst ⋙ Functor.diag C).obj X) ≫
        ((sourceSquare G₁ G₂).fst ⋙ Functor.diag C).map f := sorry

/-- The natural isomorphism making the diagonal model a square over the cospan that defines the
iterated model. -/
private def iteratedIso :
    firstComparison G₁ G₂ ⋙
        Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂) ≅
      (sourceSquare G₁ G₂).fst ⋙ Functor.diag C :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun {_ _} f ↦ iteratedIsoNaturality (G₁ := G₁) (G₂ := G₂) f)

end CategoricalPullback.DiagonalModel.Implementation

/-- The diagonal model bundled as a square over the cospan defining the iterated pullback. -/
def CategoricalPullback.DiagonalModel.iteratedSquare :
    CatCommSqOver (Functor.prod' (π₁ G₁ G₂) (π₂ G₁ G₂))
      (Functor.diag C) (CategoricalPullback.DiagonalModel.direct G₁ G₂) where
  fst := CategoricalPullback.DiagonalModel.Implementation.firstComparison G₁ G₂
  snd := (CategoricalPullback.DiagonalModel.Implementation.sourceSquare G₁ G₂).fst
  iso := CategoricalPullback.DiagonalModel.Implementation.iteratedIso G₁ G₂

/-- The canonical forward comparison from the diagonal model to the iterated model. -/
def CategoricalPullback.DiagonalModel.comparison :
    CategoricalPullback.DiagonalModel.direct G₁ G₂ ⥤
      CategoricalPullback.DiagonalModel.iterated G₁ G₂ :=
  (CategoricalPullback.DiagonalModel.iteratedSquare G₁ G₂).comparison

namespace CategoricalPullback.DiagonalModel.comparison

/-- The inner left object of the canonical diagonal-model comparison is the original
`C`-object. -/
@[simp] theorem obj.fstFst
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X).fst.fst = X.fst := sorry

/-- The inner right object of the canonical diagonal-model comparison is also the original
`C`-object. -/
@[simp] theorem obj.fstSnd
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X).fst.snd = X.fst := sorry

/-- The inner structural isomorphism of the canonical diagonal-model comparison is obtained by
comparing the two components of the original diagonal-model isomorphism. -/
@[simp] theorem obj.fstIso
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X).fst.iso =
      (CategoryTheory.Prod.fst S S).mapIso X.iso ≪≫
        ((CategoryTheory.Prod.snd S S).mapIso X.iso).symm := sorry

/-- The outer object of the canonical diagonal-model comparison is the original `C`-object. -/
@[simp] theorem obj.snd
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X).snd = X.fst := sorry

/-- The outer structural isomorphism of the canonical diagonal-model comparison is the identity. -/
@[simp] theorem obj.iso
    (X : CategoricalPullback.DiagonalModel.direct G₁ G₂) :
    ((CategoricalPullback.DiagonalModel.comparison G₁ G₂).obj X).iso =
      Iso.refl ((Functor.diag C).obj X.fst) := sorry

/-- The inner left map of the canonical diagonal-model comparison is the original first map. -/
@[simp] theorem map.fstFst
    {X Y : CategoricalPullback.DiagonalModel.direct G₁ G₂} (f : X ⟶ Y) :
    ((CategoricalPullback.DiagonalModel.comparison G₁ G₂).map f).fst.fst = f.fst := sorry

/-- The inner right map of the canonical diagonal-model comparison is the original first map. -/
@[simp] theorem map.fstSnd
    {X Y : CategoricalPullback.DiagonalModel.direct G₁ G₂} (f : X ⟶ Y) :
    ((CategoricalPullback.DiagonalModel.comparison G₁ G₂).map f).fst.snd = f.fst := sorry

/-- The outer map of the canonical diagonal-model comparison is the original first map. -/
@[simp] theorem map.snd
    {X Y : CategoricalPullback.DiagonalModel.direct G₁ G₂} (f : X ⟶ Y) :
    ((CategoricalPullback.DiagonalModel.comparison G₁ G₂).map f).snd = f.fst := sorry

end CategoricalPullback.DiagonalModel.comparison

end

end CategoryTheory.Limits
