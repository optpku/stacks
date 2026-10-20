/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.UnboundedCohomology

/-! Compatibility checks for the unbounded stage and total cohomology functors. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory ZeroObject
open RightDerived.Cochain

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasCountableProducts AddCommGrpCat.{max u w}]

variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [(fiberSectionsTotalFunctor F J).Additive]
variable [∀ n : ℕ,
    (Functor.RightDerived.Cochain.toDerived (fiberSectionsStageGamma F J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]
variable [(Functor.RightDerived.Cochain.toDerived (fiberSectionsTotalFunctor F J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]


#check (CategoryTheory.Grothendieck.fiberUnboundedPageOneFunctorNonneg F J :
    ∀ (n : ℕ) (q : ℤ),
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w})

#check (CategoryTheory.Grothendieck.fiberUnboundedPageOneDifferentialNonneg F J :
    ∀ (n : ℕ) (q : ℤ),
    fiberUnboundedPageOneFunctorNonneg F J n q ⟶
      fiberUnboundedPageOneFunctorNonneg F J (n + 1) q)

#check (CategoryTheory.Grothendieck.fiberUnboundedPageOneFunctor F J :
    ∀ (p q : ℤ),
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w})

#check (CategoryTheory.Grothendieck.fiberUnboundedPageOneFunctor_eq_of_nonneg F J :
    ∀ (p q : ℤ) (hp : 0 ≤ p),
    fiberUnboundedPageOneFunctor F J p q =
      fiberUnboundedPageOneFunctorNonneg F J p.toNat q)

#check (CategoryTheory.Grothendieck.fiberUnboundedPageOneFunctor_neg F J :
    ∀ (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    {p : ℤ} (hp : p < 0) (q : ℤ),
    IsZero ((fiberUnboundedPageOneFunctor F J p q).obj K))

#check (CategoryTheory.Grothendieck.fiberUnboundedPageOneDifferential F J :
    ∀ (p q : ℤ),
    fiberUnboundedPageOneFunctor F J p q ⟶ fiberUnboundedPageOneFunctor F J (p + 1) q)

#check (CategoryTheory.Grothendieck.fiberUnboundedAbutmentFunctor F J :
    ∀ (n : ℤ),
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w})

#check (CategoryTheory.Grothendieck.fiberUnboundedRGammaFunctor F J :
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      DerivedCategory AddCommGrpCat.{max u w})

#check (CategoryTheory.Grothendieck.fiberUnboundedAbutmentFunctor_obj F J :
    ∀ (n : ℤ) (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})),
    (fiberUnboundedAbutmentFunctor F J n).obj K =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((fiberUnboundedRGammaFunctor F J).obj K))

end CategoryTheory.Grothendieck
