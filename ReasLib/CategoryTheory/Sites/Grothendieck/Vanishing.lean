module

public import ReasLib.CategoryTheory.Sites.Grothendieck.UnboundedCohomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Functor
open HomologicalComplex ComplexShape DerivedCategory
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
variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [(fiberSectionsTotalFunctor F J).Additive]
variable [∀ n : ℕ,
    (toDerived (fiberSectionsStageGamma F J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]
variable [(toDerived (fiberSectionsTotalFunctor F J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]

/-- If fiber hypercohomology vanishes in degree `-p` for every nonnegative stage `p`,
then degree-zero hypercohomology of the total fiberwise simplicial site vanishes. -/
theorem fiber_isZero_H0_of_diagonal_vanishing
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (h : ∀ p : ℕ, IsZero ((fiberUnboundedPageOneFunctorNonneg F J p (-(p : ℤ))).obj K)) :
    IsZero ((fiberUnboundedAbutmentFunctor F J 0).obj K) :=
  sorry

/-- If derived global sections vanish on every nonnegative fiber, then derived global
sections of the total fiberwise simplicial site vanish. -/
theorem fiber_isZero_rGamma_of_stage_rGamma
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (h : ∀ p : ℕ, IsZero ((RightDerived.Cochain.functor (fiberSectionsStageGamma F J p)).obj K)) :
    IsZero ((fiberUnboundedRGammaFunctor F J).obj K) :=
  sorry

end CategoryTheory.Grothendieck
