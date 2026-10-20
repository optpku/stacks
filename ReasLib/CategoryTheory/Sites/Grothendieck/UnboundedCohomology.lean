module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.PageZeroMorphism
public import ReasLib.CategoryTheory.Homology.DoubleComplex.ProductFiltration
public import ReasLib.CategoryTheory.Sites.Grothendieck.SpectralSequence

/-!
# Unbounded cohomology on total fiberwise simplicial sites

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


/-- Nonnegative unbounded first-page target: `H^q` of `RΓ(C_n, (-)_n)`. -/
def fiberUnboundedPageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Cochain.functor (fiberSectionsStageGamma F J n) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} q

/-- The Čech differential on nonnegative unbounded first-page functors. -/
def fiberUnboundedPageOneDifferentialNonneg (n : ℕ) (q : ℤ) :
    fiberUnboundedPageOneFunctorNonneg F J n q ⟶
      fiberUnboundedPageOneFunctorNonneg F J (n + 1) q :=
  whiskerRight (Functor.RightDerived.mapNatTrans
      (DerivedCategory.Q : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
        DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
      (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))
      (whiskerRight (NatTrans.mapHomologicalComplex (fiberSectionsStageGamma_d F J n) (up ℤ))
        (DerivedCategory.Q : CochainComplex AddCommGrpCat.{max u w} ℤ ⥤
          DerivedCategory AddCommGrpCat.{max u w})))
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} q)

/-- Unbounded first-page target `K ↦ H^q(C_p, K_p)`, vanishing for `p < 0`. -/
def fiberUnboundedPageOneFunctor (p q : ℤ) :
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w} :=
  if 0 ≤ p then fiberUnboundedPageOneFunctorNonneg F J p.toNat q else
    (Functor.const (DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))).obj
      (0 : AddCommGrpCat.{max u w})

/-- Nonnegative bidegrees of `fiberUnboundedPageOneFunctor` recover the nonnegative functor. -/
theorem fiberUnboundedPageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    fiberUnboundedPageOneFunctor F J p q =
      fiberUnboundedPageOneFunctorNonneg F J p.toNat q :=
  by simp only [fiberUnboundedPageOneFunctor, if_pos hp]

/-- First-page groups in negative Čech degree vanish. -/
theorem fiberUnboundedPageOneFunctor_neg
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    {p : ℤ} (hp : p < 0) (q : ℤ) :
    IsZero ((fiberUnboundedPageOneFunctor F J p q).obj K) :=
  sorry

/-- The unbounded first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
def fiberUnboundedPageOneDifferential (p q : ℤ) :
    fiberUnboundedPageOneFunctor F J p q ⟶ fiberUnboundedPageOneFunctor F J (p + 1) q :=
  if hp : 0 ≤ p then
    eqToHom (fiberUnboundedPageOneFunctor_eq_of_nonneg F J p q hp) ≫
      fiberUnboundedPageOneDifferentialNonneg F J p.toNat q ≫
      eqToHom (congrArg (fiberUnboundedPageOneFunctorNonneg F J · q)
        (by omega)).symm ≫
      eqToHom (fiberUnboundedPageOneFunctor_eq_of_nonneg F J (p + 1) q
        (by omega)).symm
  else
    (0 : fiberUnboundedPageOneFunctor F J p q ⟶
      fiberUnboundedPageOneFunctor F J (p + 1) q)

/-- Unbounded cohomology `K ↦ H^n(C_total, K)`. -/
def fiberUnboundedAbutmentFunctor (n : ℤ) :
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Cochain.functor (fiberSectionsTotalFunctor F J) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} n

/-- Unbounded `RΓ(C_total, -)` as the total right derived functor of `Γ(C_total, -)`. -/
def fiberUnboundedRGammaFunctor :
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      DerivedCategory AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Cochain.functor (fiberSectionsTotalFunctor F J)

/-- Evaluation of `fiberUnboundedAbutmentFunctor` is homology of unbounded `RΓ`. -/
theorem fiberUnboundedAbutmentFunctor_obj
    (n : ℤ) (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) :
    (fiberUnboundedAbutmentFunctor F J n).obj K =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((fiberUnboundedRGammaFunctor F J).obj K) :=
  rfl


/-- Derived global sections of a K-injective complex of injective sheaves on a total
fiberwise site are represented by the product total of the fiber-sections bicomplex. -/
theorem fiberRGammaIsoProductTotal
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K) :
    IsIsomorphic ((fiberUnboundedRGammaFunctor F J).obj K)
      (DerivedCategory.Q.obj (HomologicalComplex₂.ProductTotal.complex (fiberSectionsBicomplex F J I))) :=
  sorry

/-- The product-tail filtration of the stage-sections bicomplex of an unbounded
K-injective injective-term representative admits a spectral sequence whose first page
is stage hypercohomology with its canonical alternating-coface differential. -/
theorem fiberExists_spectralSequence
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K) :
    ∃ (E : CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (hE : IsAssociated (HomologicalComplex₂.ProductTotal.filtration (fiberSectionsBicomplex F J I)) E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅ (fiberUnboundedPageOneFunctor F J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (fiberUnboundedPageOneDifferential F J p q).app K =
          (E.page 1).d (p, q) (p + 1, q) ≫ (pageOneIso (p + 1) q).hom :=
  sorry

/-- The product-tail spectral sequences can be chosen as one functor on all complexes,
with association data compatible with the canonical filtered product-total maps and
simultaneous natural first-page comparisons for K-injective injective-term representatives. -/
theorem fiberSpectralSequence_functorial :
    ∃ (E : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
        CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (A : ∀ I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ,
        Association (HomologicalComplex₂.ProductTotal.filtration (fiberSectionsBicomplex F J I))
          (E.obj I))
      (pageOneIso : ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
        [I.IsKInjective] [∀ n, Injective (I.X n)]
        (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
        (hK : DerivedCategory.Q.obj I ≅ K) (p q : ℤ),
        ((E.obj I).page 1).X (p, q) ≅ (fiberUnboundedPageOneFunctor F J p q).obj K),
      (∀ {I I' : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ} (fI : I ⟶ I'),
        Page.Zero.IsCompatible (A I).toComparison (A I').toComparison
          (HomologicalComplex₂.ProductTotal.filtrationMap ((fiberSectionsBicomplexFunctor F J).map fI))
          (E.map fI)) ∧
      (∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
        [I.IsKInjective] [∀ n, Injective (I.X n)]
        (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
        (hK : DerivedCategory.Q.obj I ≅ K) (p q : ℤ),
        (pageOneIso I K hK p q).hom ≫ (fiberUnboundedPageOneDifferential F J p q).app K =
          ((E.obj I).page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso I K hK (p + 1) q).hom) ∧
      ∀ {I I' : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ}
        [I.IsKInjective] [I'.IsKInjective]
        [∀ n, Injective (I.X n)] [∀ n, Injective (I'.X n)]
        {K L : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})}
        (hK : DerivedCategory.Q.obj I ≅ K) (hL : DerivedCategory.Q.obj I' ≅ L)
        (fI : I ⟶ I') (p q : ℤ),
        ((E.map fI).hom 1).f (p, q) ≫ (pageOneIso I' L hL p q).hom =
          (pageOneIso I K hK p q).hom ≫
            (fiberUnboundedPageOneFunctor F J p q).map
              (hK.inv ≫ DerivedCategory.Q.map fI ≫ hL.hom) :=
  sorry

end CategoryTheory.Grothendieck
