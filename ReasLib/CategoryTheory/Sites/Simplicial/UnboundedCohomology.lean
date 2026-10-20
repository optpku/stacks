/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.PageZeroMorphism
public import ReasLib.CategoryTheory.Homology.DoubleComplex.ProductFiltration
public import ReasLib.CategoryTheory.Sites.Simplicial.Bicomplex

/-!
# Unbounded cohomology on total simplicial sites

Stage hypercohomology is the first page of the product-tail spectral sequence of
a K-injective complex of injective abelian sheaves, without a convergence assertion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory ZeroObject FilteredComplex
open RightDerived.Cochain
open scoped HomologicalComplex₂

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


/-- Nonnegative unbounded first-page target: `H^q` of `RΓ(C_n, (-)_n)`. -/
def unboundedPageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Cochain.functor (sectionsStageGamma C J n) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} q

/-- The Čech differential on nonnegative unbounded first-page functors. -/
def unboundedPageOneDifferentialNonneg (n : ℕ) (q : ℤ) :
    unboundedPageOneFunctorNonneg C J n q ⟶ unboundedPageOneFunctorNonneg C J (n + 1) q :=
  whiskerRight (Functor.RightDerived.mapNatTrans
      (DerivedCategory.Q : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
        DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
      (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))
      (whiskerRight (NatTrans.mapHomologicalComplex (sectionsStageGamma_d C J n) (up ℤ))
        (DerivedCategory.Q : CochainComplex AddCommGrpCat.{max u w} ℤ ⥤
          DerivedCategory AddCommGrpCat.{max u w})))
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} q)

/-- Unbounded first-page target `K ↦ H^q(C_p, K_p)`, vanishing for `p < 0`. -/
def unboundedPageOneFunctor (p q : ℤ) :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w} :=
  if 0 ≤ p then unboundedPageOneFunctorNonneg C J p.toNat q else
    (Functor.const (DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))).obj
      (0 : AddCommGrpCat.{max u w})

/-- Nonnegative bidegrees of `unboundedPageOneFunctor` recover the nonnegative functor. -/
theorem unboundedPageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    unboundedPageOneFunctor C J p q = unboundedPageOneFunctorNonneg C J p.toNat q :=
  by simp only [unboundedPageOneFunctor, if_pos hp]

/-- First-page groups in negative Čech degree vanish. -/
theorem unboundedPageOneFunctor_neg
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    {p : ℤ} (hp : p < 0) (q : ℤ) :
    IsZero ((unboundedPageOneFunctor C J p q).obj K) :=
  sorry

/-- The unbounded first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
def unboundedPageOneDifferential (p q : ℤ) :
    unboundedPageOneFunctor C J p q ⟶ unboundedPageOneFunctor C J (p + 1) q :=
  if hp : 0 ≤ p then
    eqToHom (unboundedPageOneFunctor_eq_of_nonneg C J p q hp) ≫
      unboundedPageOneDifferentialNonneg C J p.toNat q ≫
      eqToHom (congrArg (unboundedPageOneFunctorNonneg C J · q)
        (by omega)).symm ≫
      eqToHom (unboundedPageOneFunctor_eq_of_nonneg C J (p + 1) q (by omega)).symm
  else
    (0 : unboundedPageOneFunctor C J p q ⟶ unboundedPageOneFunctor C J (p + 1) q)

/-- Unbounded cohomology `K ↦ H^n(C_total, K)`, for comparison with homology of `Tot_π`. -/
def unboundedAbutmentFunctor (n : ℤ) :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Cochain.functor (globalSectionsTotalFunctor C J) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} n

/-- Unbounded `RΓ(C_total, -)` as the total right derived functor of `Γ(C_total, -)`. -/
def unboundedRGammaFunctor :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      DerivedCategory AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Cochain.functor (globalSectionsTotalFunctor C J)

/-- Evaluation of `unboundedAbutmentFunctor` is homology of unbounded `RΓ`. -/
theorem unboundedAbutmentFunctor_obj
    (n : ℤ) (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    (unboundedAbutmentFunctor C J n).obj K =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((unboundedRGammaFunctor C J).obj K) :=
  rfl


/-- Derived global sections of an unbounded complex represented by a K-injective complex
of injective sheaves are represented by the product total of its stage-sections bicomplex. -/
theorem rGammaIsoProductTotal
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K) :
    IsIsomorphic ((unboundedRGammaFunctor C J).obj K)
      (DerivedCategory.Q.obj (HomologicalComplex₂.ProductTotal.complex (sectionsBicomplex C J I))) :=
  sorry

/-- The product-tail filtration of the stage-sections bicomplex of an unbounded
K-injective injective-term representative admits a spectral sequence whose first page
is stage hypercohomology with its canonical alternating-coface differential. -/
theorem unboundedExists_spectralSequence
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K) :
    ∃ (E : CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (hE : IsAssociated (HomologicalComplex₂.ProductTotal.filtration (sectionsBicomplex C J I)) E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅ (unboundedPageOneFunctor C J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (unboundedPageOneDifferential C J p q).app K =
          (E.page 1).d (p, q) (p + 1, q) ≫ (pageOneIso (p + 1) q).hom :=
  sorry

/-- The product-tail spectral sequences can be chosen as one functor on all complexes,
with association data compatible with the canonical filtered product-total maps and
simultaneous natural first-page comparisons for K-injective injective-term representatives. -/
theorem unboundedSpectralSequence_functorial :
    ∃ (E : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
        CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (A : ∀ I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ,
        Association (HomologicalComplex₂.ProductTotal.filtration (sectionsBicomplex C J I))
          (E.obj I))
      (pageOneIso : ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
        [I.IsKInjective] [∀ n, Injective (I.X n)]
        (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
        (hK : DerivedCategory.Q.obj I ≅ K) (p q : ℤ),
        ((E.obj I).page 1).X (p, q) ≅ (unboundedPageOneFunctor C J p q).obj K),
      (∀ {I I' : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ} (fI : I ⟶ I'),
        Page.Zero.IsCompatible (A I).toComparison (A I').toComparison
          (HomologicalComplex₂.ProductTotal.filtrationMap ((sectionsBicomplexFunctor C J).map fI))
          (E.map fI)) ∧
      (∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
        [I.IsKInjective] [∀ n, Injective (I.X n)]
        (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
        (hK : DerivedCategory.Q.obj I ≅ K) (p q : ℤ),
        (pageOneIso I K hK p q).hom ≫ (unboundedPageOneDifferential C J p q).app K =
          ((E.obj I).page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso I K hK (p + 1) q).hom) ∧
      ∀ {I I' : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ}
        [I.IsKInjective] [I'.IsKInjective]
        [∀ n, Injective (I.X n)] [∀ n, Injective (I'.X n)]
        {K L : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})}
        (hK : DerivedCategory.Q.obj I ≅ K) (hL : DerivedCategory.Q.obj I' ≅ L)
        (fI : I ⟶ I') (p q : ℤ),
        ((E.map fI).hom 1).f (p, q) ≫ (pageOneIso I' L hL p q).hom =
          (pageOneIso I K hK p q).hom ≫
            (unboundedPageOneFunctor C J p q).map
              (hK.inv ≫ DerivedCategory.Q.map fI ≫ hL.hom) :=
  sorry

end CategoryTheory.SimplicialSites
