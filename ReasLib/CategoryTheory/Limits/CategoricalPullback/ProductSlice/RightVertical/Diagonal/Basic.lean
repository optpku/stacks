/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Comparison
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.ComparisonConstruction
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.LeftDomain
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.Swap
public import ReasLib.CategoryTheory.Functor.OverIso

/-!
# Product-slice diagonal comparison

This file owns the explicit chain of over-base equivalences behind the product-slice diagonal
comparison. The equivalence instance and its selected inverse are kept in `Diagonal.Equivalence`.
-/

@[expose] public section

universe vC vXS uC uXS

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace Limits.CategoricalPullback.ProductSlice

section RightVertical

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {C : Type uC} [Category.{vC} C] [Limits.HasBinaryProducts C]
variable {XS : Type uXS} [Category.{vXS} XS]
variable {U V : C} {gU : Over U ⥤ XS} {gV : Over V ⥤ XS} {xp : XS ⥤ C}

namespace Diagonal.Implementation

/-- The objectwise base comparison between the middle leg-congruence model and the
product-of-slices model. Both constructions retain the common source object definitionally. -/
private noncomputable def middleBaseIsoApp
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (P : (Over.forget U) ⊡ (Over.forget V)) :
    ((CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
        (π₁ (gU ⋙ xp) (gV ⋙ xp) ⋙ Over.forget U)).obj P ≅
      ((CategoricalPullback.ProductSlice.equivalence U V).functor ⋙
        Over.forget (Limits.prod U V)).obj P :=
  Iso.refl _

/-- The explicit middle-base comparisons are natural in product-of-slices morphisms. -/
private theorem middleBaseIsoApp_naturality
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    {P Q : (Over.forget U) ⊡ (Over.forget V)} (φ : P ⟶ Q) :
    ((CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
          (π₁ (gU ⋙ xp) (gV ⋙ xp) ⋙ Over.forget U)).map φ ≫
        (middleBaseIsoApp eU eV Q).hom =
      (middleBaseIsoApp eU eV P).hom ≫
        ((CategoricalPullback.ProductSlice.equivalence U V).functor ⋙
          Over.forget (Limits.prod U V)).map φ := sorry

end Diagonal.Implementation

/-- The middle leg-congruence and product-of-slices base projections are explicitly naturally
isomorphic. -/
noncomputable def Diagonal.middleBaseIso
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    (CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
        (π₁ (gU ⋙ xp) (gV ⋙ xp) ⋙ Over.forget U) ≅
      (CategoricalPullback.ProductSlice.equivalence U V).functor ⋙
        Over.forget (Limits.prod U V) :=
  NatIso.ofComponents
    (Diagonal.Implementation.middleBaseIsoApp eU eV)
    (fun φ ↦ Diagonal.Implementation.middleBaseIsoApp_naturality eU eV φ)

/-- Every object component of the middle-base comparison is the identity isomorphism. -/
@[simp]
theorem Diagonal.middleBaseIso.app
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (P : (Over.forget U) ⊡ (Over.forget V)) :
    (Diagonal.middleBaseIso eU eV).app P = Iso.refl _ := sorry

/-- The forward component of the middle-base comparison is its explicit objectwise identity
comparison. -/
@[simp]
theorem Diagonal.middleBaseIso.hom.app
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (P : (Over.forget U) ⊡ (Over.forget V)) :
    (Diagonal.middleBaseIso eU eV).hom.app P = 𝟙 _ := sorry

/-- The inverse component of the middle-base comparison is its explicit objectwise identity
comparison. -/
@[simp]
theorem Diagonal.middleBaseIso.inv.app
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (P : (Over.forget U) ⊡ (Over.forget V)) :
    (Diagonal.middleBaseIso eU eV).inv.app P = 𝟙 _ := sorry

namespace Diagonal.Implementation

/-- The canonical swap of `gV ⊡ gU`, regarded over the first projection to the `U`-slice base. -/
private noncomputable def swapStep :
    Functor.OverIso (π₂ gV gU ⋙ Over.forget U)
      (π₁ gU gV ⋙ Over.forget U) :=
  Functor.OverIso.mk (CategoricalPullback.swap gV gU) (Iso.refl _)

/-- The canonical diagonal comparison for `gU` and `gV`, regarded over the middle
product-of-base projection. -/
private noncomputable def diagonalStep :
    Functor.OverIso (π₁ gU gV ⋙ Over.forget U)
      (π₁ (CategoricalPullback.toDiagonal gU gV xp) (Δₚ xp) ⋙
        (π₁ (gU ⋙ xp) (gV ⋙ xp) ⋙ Over.forget U)) :=
  Functor.OverIso.mk
    (CategoricalPullback.diagonalComparison gU gV xp) (Iso.refl _)

/-- Transport the diagonal comparison along the two leg isomorphisms, using the explicit
middle-base comparison to retain the projection over `C/(U × V)`. -/
private noncomputable def legDomainStep
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :=
  Functor.OverIso.mk
    (CategoricalPullback.DomainChange.Left.equivalence
      (CategoricalPullback.LegChange.equivalence eU.symm eV.symm)
      (CategoricalPullback.toDiagonal gU gV xp) (Δₚ xp)).inverse
    (CategoricalPullback.DomainChange.Left.equivalence.inverseFstIso
      (CategoricalPullback.LegChange.equivalence eU.symm eV.symm)
      (CategoricalPullback.toDiagonal gU gV xp) (Δₚ xp)
      (π₁ (gU ⋙ xp) (gV ⋙ xp) ⋙ Over.forget U)
      ((CategoricalPullback.ProductSlice.equivalence U V).functor ⋙
        Over.forget (Limits.prod U V))
      (Diagonal.middleBaseIso eU eV))

/-- Transport the left endpoint from the product-of-slices model to the product-slice model. -/
private noncomputable def productSliceDomainStep
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :=
  Functor.OverIso.mk
    (CategoricalPullback.DomainChange.Left.equivalence
      (CategoricalPullback.ProductSlice.equivalence U V).symm
      ((CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
        CategoricalPullback.toDiagonal gU gV xp)
      (Δₚ xp)).inverse
    (CategoricalPullback.DomainChange.Left.equivalence.inverseFstIso
      (CategoricalPullback.ProductSlice.equivalence U V).symm
      ((CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
        CategoricalPullback.toDiagonal gU gV xp)
      (Δₚ xp)
      ((CategoricalPullback.ProductSlice.equivalence U V).functor ⋙
        Over.forget (Limits.prod U V))
      (Over.forget (Limits.prod U V))
      ((CategoricalPullback.ProductSlice.equivalence U V).symm.funInvIdAssoc
        (Over.forget (Limits.prod U V))))

/-- Replace the transported first leg by the explicit product-slice right vertical. -/
private noncomputable def rightVerticalLegStep
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    Functor.OverIso
      (π₁ (CategoricalPullback.ProductSlice.fromProduct U V ⋙
          (CategoricalPullback.LegChange.equivalence eU.symm eV.symm).functor ⋙
          CategoricalPullback.toDiagonal gU gV xp)
        (Δₚ xp) ⋙ Over.forget (Limits.prod U V))
      (π₁ (RightVertical.functor (RightVertical.baseIso eU eV))
        (Δₚ xp) ⋙ Over.forget (Limits.prod U V)) :=
  Functor.OverIso.mk
    (CategoricalPullback.LegChange.equivalence
      (RightVertical.comparisonIso eU eV).symm (Iso.refl (Δₚ xp))).inverse
    (Functor.isoWhiskerRight
      (CategoricalPullback.LegChange.equivalence.inverseFstIso
        (RightVertical.comparisonIso eU eV).symm (Iso.refl (Δₚ xp)))
      (Over.forget (Limits.prod U V)))

end Diagonal.Implementation

/-- The product-slice diagonal comparison, together with its canonical compatibility over `C`.
The functor and base isomorphism are owned by the same `Functor.OverIso`, so downstream transport
does not depend on reassociating the five constituent equivalences by definitional equality. -/
noncomputable def Diagonal.comparisonOverBase
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    Functor.OverIso (π₂ gV gU ⋙ Over.forget U)
      (π₁ (RightVertical.functor (RightVertical.baseIso eU eV))
        (Δₚ xp) ⋙ Over.forget (Limits.prod U V)) :=
  (Diagonal.Implementation.swapStep (U := U) (V := V) (gU := gU) (gV := gV)).comp
    ((Diagonal.Implementation.diagonalStep
        (U := U) (V := V) (gU := gU) (gV := gV) (xp := xp)).comp
      ((Diagonal.Implementation.legDomainStep
          (U := U) (V := V) (gU := gU) (gV := gV) (xp := xp) eU eV).comp
        ((Diagonal.Implementation.productSliceDomainStep
            (U := U) (V := V) (gU := gU) (gV := gV) (xp := xp) eU eV).comp
          (Diagonal.Implementation.rightVerticalLegStep
            (U := U) (V := V) (gU := gU) (gV := gV) (xp := xp) eU eV))))

/-- The comparison from `gV ⊡ gU` to the diagonal base change built from `C/(U × V)`. -/
noncomputable def Diagonal.comparison
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V) :
    gV ⊡ gU ⥤
      (RightVertical.functor (RightVertical.baseIso eU eV)) ⊡
        (Δₚ xp) :=
  (Diagonal.comparisonOverBase eU eV).functor

end RightVertical

end Limits.CategoricalPullback.ProductSlice

end CategoryTheory
