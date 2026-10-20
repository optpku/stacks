/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Comparison.Equivalence
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical

/-!
# Product-slice source square

This leaf owns the product-slice pseudo-pullback source square, its base
comparison, and its projection-level normalization API.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
open scoped Pseudofunctor.StrongTrans

open Limits.CategoricalPullback.ProductSlice

variable {C : Type u} [Category.{v} C]

/-! ### Product-slice source square with explicit base projection isomorphism -/
namespace FiberedCategoryOver.Groupoids.ProductSlice

section ProductSliceSourceSquare

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable [Limits.HasBinaryProducts C]
variable {U V : C}

namespace Implementation

/-- The left pulled-back base projection agrees with the product-slice projection. -/
private theorem leftBaseObjEq
    (X : FiberedCategoryOver.Groupoids C)
    (G : slice U ⟶ X)
    (a : Over (Limits.prod U V)) :
    (FiberedCategoryOver.Groupoids.base C).p.obj
        ((FiberedCategoryOver.Groupoids.toFunctor
          ((slice.pullback (Limits.prod.fst (X := U) (Y := V)) G) ≫
            X.baseProjection)).obj a) =
      (slice (Limits.prod U V)).p.obj a := sorry
/- Proof strategy: evaluate `FiberedCategoryOver.Groupoids.comm G` at
`(Over.map Limits.prod.fst).obj a`. -/

/-- The right pulled-back base projection agrees with the product-slice projection. -/
private theorem rightBaseObjEq
    (X : FiberedCategoryOver.Groupoids C)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    (FiberedCategoryOver.Groupoids.base C).p.obj
        ((FiberedCategoryOver.Groupoids.toFunctor
          ((slice.pullback (Limits.prod.snd (X := U) (Y := V)) G') ≫
            X.baseProjection)).obj a) =
      (slice (Limits.prod U V)).p.obj a := sorry
/- Proof strategy: evaluate `FiberedCategoryOver.Groupoids.comm G'` at
`(Over.map Limits.prod.snd).obj a`. -/

/-- The product-slice base isomorphism lifted along the canonical section of the
universe-resized identity fibration. -/
private noncomputable def liftedBaseIso
    (X : FiberedCategoryOver.Groupoids C)
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    FiberedCategoryOver.Groupoids.toFunctor
        ((slice.pullback Limits.prod.fst G) ≫ X.baseProjection) ≅
      FiberedCategoryOver.Groupoids.toFunctor
        ((slice.pullback Limits.prod.snd G') ≫ X.baseProjection) :=
  Functor.isoWhiskerRight
    (RightVertical.baseIso
      (FiberedCategoryOver.Groupoids.commIso G)
      (FiberedCategoryOver.Groupoids.commIso G'))
    (FiberedCategoryOver.Groupoids.baseSection C)

/-- Every component of the explicit product-slice base isomorphism lies over the identity of its
base object. -/
private theorem liftedBaseIso.homIsLift
    (X : FiberedCategoryOver.Groupoids C)
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    (FiberedCategoryOver.Groupoids.base C).p.IsHomLift
      (𝟙 ((slice (Limits.prod U V)).p.obj a))
      ((liftedBaseIso X G G').hom.app a) := sorry
/- Proof strategy: use `IsHomLift.of_fac'` with `leftBaseObjEq` and
`rightBaseObjEq`; reduce the two equality transports by proof irrelevance. -/

end Implementation

/-- The canonical owner isomorphism between the two product-slice legs over `C`. Its underlying
natural isomorphism is `RightVertical.baseIso`. -/
@[stacks 04SF "product-slice base comparison"]
noncomputable def baseIso
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    ((slice.pullback Limits.prod.fst G) ≫ X.baseProjection) ≅
      ((slice.pullback Limits.prod.snd G') ≫ X.baseProjection) :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (Implementation.liftedBaseIso X G G')
      (Implementation.liftedBaseIso.homIsLift X G G'))

/-- Forgetting `baseIso` recovers its canonical underlying natural isomorphism. -/
@[simp] theorem baseIso.toFunctorIso
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    FiberedCategoryOver.Groupoids.toFunctorIso (baseIso (X := X) G G') =
      Functor.isoWhiskerRight
        (RightVertical.baseIso
          (FiberedCategoryOver.Groupoids.commIso G)
          (FiberedCategoryOver.Groupoids.commIso G'))
        (FiberedCategoryOver.Groupoids.baseSection C) := sorry
/- Proof strategy: unfold `baseIso` and the owner/based-functor conversion APIs; the
underlying natural isomorphism is definitionally the supplied one. -/

/-- The forward component of the source-square base comparison is the image under the canonical
base section of the two slice-leg base comparisons. -/
@[simp]
theorem baseIso.toFunctorIso.hom.app
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    (FiberedCategoryOver.Groupoids.toFunctorIso (baseIso (X := X) G G')).hom.app a =
      (FiberedCategoryOver.Groupoids.baseSection C).map
        ((FiberedCategoryOver.Groupoids.commIso G).hom.app
            ((Over.map Limits.prod.fst).obj a) ≫
          (FiberedCategoryOver.Groupoids.commIso G').inv.app
            ((Over.map Limits.prod.snd).obj a)) := sorry

/-- The inverse component of the source-square base comparison is the image under the canonical
base section of the reverse two slice-leg base comparisons. -/
@[simp]
theorem baseIso.toFunctorIso.inv.app
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    (FiberedCategoryOver.Groupoids.toFunctorIso (baseIso (X := X) G G')).inv.app a =
      (FiberedCategoryOver.Groupoids.baseSection C).map
        ((FiberedCategoryOver.Groupoids.commIso G').hom.app
            ((Over.map Limits.prod.snd).obj a) ≫
          (FiberedCategoryOver.Groupoids.commIso G).inv.app
            ((Over.map Limits.prod.fst).obj a)) := sorry

/-- The product-slice source square for comparison with the diagonal target.

Read it as two ways to recover the base object of a point over `U × V`:

Writing `P := slice (Limits.prod U V)`,
`p₁ := slice.pullback Limits.prod.fst G`, and
`p₂ := slice.pullback Limits.prod.snd G'`, the square is

```
                   p₁
       P ─────────────────────▶ X
       │                        │
    p₂ │                        │ X.baseProjection
       ▼                        ▼
       X ─────────────────────▶ C
              X.baseProjection
```

The structural `2`-cell `baseIso G G'` identifies these two routes. -/
@[stacks 04SF "product-slice source pseudo-pullback cone"]
noncomputable def sourceSquare
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection where
  pt := slice (Limits.prod U V)
  fst := slice.pullback (Limits.prod.fst (X := U) (Y := V)) G
  snd := slice.pullback (Limits.prod.snd (X := U) (Y := V)) G'
  iso := baseIso (X := X) G G'

/-- The apex of the product-slice source square is the category fibred in groupoids associated
to the product-slice projection. -/
@[simp]
theorem sourceSquare.pt
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    (sourceSquare (X := X) G G').pt =
      slice (Limits.prod U V) := sorry

/-- The first leg of the product-slice source square is pullback along the first product
projection. -/
@[simp]
theorem sourceSquare.fst
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    (sourceSquare (X := X) G G').fst =
      slice.pullback (Limits.prod.fst (X := U) (Y := V)) G := sorry

/-- The second leg of the product-slice source square is pullback along the second product
projection. -/
@[simp]
theorem sourceSquare.snd
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    (sourceSquare (X := X) G G').snd =
      slice.pullback (Limits.prod.snd (X := U) (Y := V)) G' := sorry

/-- The comparison `2`-isomorphism of the product-slice source square is its canonical base
isomorphism. -/
@[simp]
theorem sourceSquare.iso
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    (sourceSquare (X := X) G G').iso = baseIso (X := X) G G' := sorry

/-- The canonical morphism from the product-slice source square to the chosen self-
two-fibre-product cone. It is the universal readable cone morphism, so its apex map and
comparison modification are governed by `PseudoPullbackCone.lift.hom`. -/
@[stacks 04SF "canonical product-slice cone comparison"]
noncomputable def sourceSquare.coneComparison
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X) (G' : slice V ⟶ X) :
    sourceSquare (X := X) G G' ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection :=
  PseudoPullbackCone.lift.hom
    (sourceSquare (X := X) G G')
    (CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)

/-- The apex projection of `sourceSquare` is the product-slice forgetful functor. -/
@[simp] theorem sourceSquare.pt.p
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    (sourceSquare (X := X) G G').pt.p =
      Over.forget (Limits.prod U V) := sorry
/- Proof strategy: unfold only `sourceSquare`, then use
`FiberedCategoryOver.Groupoids.ofFunctor.p` for the apex projection. -/

namespace sourceSquare.Implementation

/-- The objectwise comparison between the source-square apex projection and the product-slice
forgetful functor. The bundled apex retains the same underlying slice object definitionally. -/
private noncomputable def ptPIsoApp
    (X : FiberedCategoryOver.Groupoids C)
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    (sourceSquare (X := X) G G').pt.p.obj a ≅
      (Over.forget (Limits.prod U V)).obj a :=
  Iso.refl _

/-- The explicit source-square apex-projection comparisons are natural. -/
private theorem ptPIsoApp_naturality
    (X : FiberedCategoryOver.Groupoids C)
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    {a b : Over (Limits.prod U V)} (f : a ⟶ b) :
    (sourceSquare (X := X) G G').pt.p.map f ≫
        (ptPIsoApp X G G' b).hom =
      (ptPIsoApp X G G' a).hom ≫
        (Over.forget (Limits.prod U V)).map f := sorry

end sourceSquare.Implementation

/-- The source-square apex projection is explicitly naturally isomorphic to the product-slice
forgetful functor. -/
@[stacks 04SF "product-slice apex projection comparison"]
noncomputable def sourceSquare.ptPIso
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    (sourceSquare (X := X) G G').pt.p ≅
      Over.forget (Limits.prod U V) :=
  NatIso.ofComponents
    (sourceSquare.Implementation.ptPIsoApp X G G')
    (fun f ↦ sourceSquare.Implementation.ptPIsoApp_naturality X G G' f)

/-- Every object component of the source-square apex-projection comparison is the identity
isomorphism. -/
@[simp]
theorem sourceSquare.ptPIso.app
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    (sourceSquare.ptPIso (X := X) G G').app a = Iso.refl _ := sorry

/-- The forward component of the source-square apex-projection comparison is its explicit
objectwise identity comparison. -/
@[simp]
theorem sourceSquare.ptPIso.hom.app
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    (sourceSquare.ptPIso (X := X) G G').hom.app a = 𝟙 _ := sorry

/-- The inverse component of the source-square apex-projection comparison is its explicit
objectwise identity comparison. -/
@[simp]
theorem sourceSquare.ptPIso.inv.app
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    (a : Over (Limits.prod U V)) :
    (sourceSquare.ptPIso (X := X) G G').inv.app a = 𝟙 _ := sorry

/-- The inverse Remark-4.35.8 projection formula specialized to a two-fibre product whose left leg
starts at `sourceSquare`. -/
@[stacks 04SF "inverse projection comparison for the product-slice source"]
noncomputable def sourceSquare.inverseLeftBaseIso
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X)
    {T Y : FiberedCategoryOver.Groupoids C}
    (H : (sourceSquare (X := X) G G').pt ⟶ T) (Dg : Y ⟶ T) :
    (BasedCategory.PseudoPullback.Comparison.equivalence
      (FiberedCategoryOver.Groupoids.toBasedFunctor H)
      (FiberedCategoryOver.Groupoids.toBasedFunctor Dg)).inverse ⋙
        FiberedCategoryOver.Groupoids.p
          (CategoryTheory.TwoFibreProduct.apex H Dg) ≅
      π₁ (FiberedCategoryOver.Groupoids.toFunctor H) (FiberedCategoryOver.Groupoids.toFunctor Dg) ⋙
        Over.forget (Limits.prod U V) :=
  BasedCategory.PseudoPullback.Comparison.equivalence.inverse.fstBaseIso
    (FiberedCategoryOver.Groupoids.toBasedFunctor H)
    (FiberedCategoryOver.Groupoids.toBasedFunctor Dg) ≪≫
    Functor.isoWhiskerLeft
      (π₁ (FiberedCategoryOver.Groupoids.toFunctor H) (FiberedCategoryOver.Groupoids.toFunctor Dg))
      (sourceSquare.ptPIso (X := X) G G')

end ProductSliceSourceSquare

end FiberedCategoryOver.Groupoids.ProductSlice

end CategoryTheory
