module

public import ReasLib.CategoryTheory.Sites.Simplicial.UnboundedCohomology

/-! Compatibility checks for the unbounded stage and total cohomology functors. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory ZeroObject
open RightDerived.Cochain

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]
variable [HasCountableProducts AddCommGrpCat.{max u w}]

variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [(globalSectionsTotalFunctor C J).Additive]
variable [∀ n : ℕ,
    (Functor.RightDerived.Cochain.toDerived (sectionsStageGamma C J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]
variable [(Functor.RightDerived.Cochain.toDerived (globalSectionsTotalFunctor C J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]


#check (CategoryTheory.SimplicialSites.unboundedPageOneFunctorNonneg C J :
    ∀ (n : ℕ) (q : ℤ),
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w})

#check (CategoryTheory.SimplicialSites.unboundedPageOneDifferentialNonneg C J :
    ∀ (n : ℕ) (q : ℤ),
    unboundedPageOneFunctorNonneg C J n q ⟶ unboundedPageOneFunctorNonneg C J (n + 1) q)

#check (CategoryTheory.SimplicialSites.unboundedPageOneFunctor C J :
    ∀ (p q : ℤ),
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w})

#check (CategoryTheory.SimplicialSites.unboundedPageOneFunctor_eq_of_nonneg C J :
    ∀ (p q : ℤ) (hp : 0 ≤ p),
    unboundedPageOneFunctor C J p q = unboundedPageOneFunctorNonneg C J p.toNat q)

#check (CategoryTheory.SimplicialSites.unboundedPageOneFunctor_neg C J :
    ∀ (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    {p : ℤ} (hp : p < 0) (q : ℤ),
    IsZero ((unboundedPageOneFunctor C J p q).obj K))

#check (CategoryTheory.SimplicialSites.unboundedPageOneDifferential C J :
    ∀ (p q : ℤ),
    unboundedPageOneFunctor C J p q ⟶ unboundedPageOneFunctor C J (p + 1) q)

#check (CategoryTheory.SimplicialSites.unboundedAbutmentFunctor C J :
    ∀ (n : ℤ),
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w})

#check (CategoryTheory.SimplicialSites.unboundedRGammaFunctor C J :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      DerivedCategory AddCommGrpCat.{max u w})

#check (CategoryTheory.SimplicialSites.unboundedAbutmentFunctor_obj C J :
    ∀ (n : ℤ) (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})),
    (unboundedAbutmentFunctor C J n).obj K =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((unboundedRGammaFunctor C J).obj K))

end CategoryTheory.SimplicialSites
