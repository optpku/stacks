module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Filtration.Complex.Definition
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Filtration.Preadditive
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right
public import ReasLib.CategoryTheory.Homology.DoubleComplex.ProductTotal
public import stacks_project.Chap85.Lemma_85_8_3_Bicomplex

/-!
# Product total of the Čech–injective bicomplex

In Situation 85.3.3 case A, the product total `Tot_π(A)` of the double complex
`A^{p,q} = Γ(C_p, I^q_p)` represents unbounded `RΓ(C_total, -)` on a K-injective
complex of injective sheaves. The product-tail filtration
`F^i Tot^n_π(A) = ∏_{p+q=n, p ≥ i} A^{p,q}` is recorded as the kernel of the
complementary antidiagonal projections, and the unbounded first-page functors
are the total right derived functors of stagewise global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open HomologicalComplex ComplexShape DerivedCategory ZeroObject
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

/-- The product total `Tot_π(A)` of the Čech–injective bicomplex `A^{p,q} = Γ(C_p, I^q_p)`. -/
def sectionsProductTotal
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)] :
    CochainComplex AddCommGrpCat.{max u w} ℤ :=
  HomologicalComplex₂.ProductTotal.complex (sectionsBicomplex C J I)

/-- Antidiagonal projection `Tot^{p+q}_π(A) ⟶ A^{p,q}`. -/
def sectionsProductTotal_π
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (p q : ℤ) :
    (sectionsProductTotal C J I).X (p + q) ⟶
      ((sectionsBicomplex C J I).X p).X q :=
  HomologicalComplex₂.ProductTotal.π (sectionsBicomplex C J I) p q

/-- Antidiagonal projection at an identified total degree. -/
def sectionsProductTotal_πOfEq
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (p q : ℤ) {n : ℤ} (h : p + q = n) :
    (sectionsProductTotal C J I).X n ⟶ ((sectionsBicomplex C J I).X p).X q :=
  HomologicalComplex₂.ProductTotal.πOfEq (sectionsBicomplex C J I) p q h

/-- The source product `∏_{p+q=n, p ≥ i} A^{p,q}`. -/
def sectionsProductStage
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    (n i : ℤ) :
    AddCommGrpCat.{max u w} :=
  ∏ᶜ fun p : {p : ℤ // i ≤ p} ↦ ((sectionsBicomplex C J I).X p.1).X (n - p.1)

/-- Projection from the source product onto a retained bidegree. -/
def sectionsProductStage_π
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    (n i : ℤ) (p : {p : ℤ // i ≤ p}) :
    sectionsProductStage C J I n i ⟶ ((sectionsBicomplex C J I).X p.1).X (n - p.1) :=
  Pi.π (fun q : {q : ℤ // i ≤ q} ↦ ((sectionsBicomplex C J I).X q.1).X (n - q.1)) p

/-- The complementary product of discarded antidiagonal summands `p < i`. -/
def sectionsProductComplement
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    (n i : ℤ) :
    AddCommGrpCat.{max u w} :=
  ∏ᶜ fun p : {p : ℤ // p < i} ↦ ((sectionsBicomplex C J I).X p.1).X (n - p.1)

/-- The canonical map `Tot^n_π(A) ⟶ ∏_{p+q=n, p < i} A^{p,q}`. -/
def sectionsProductComplement_π
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (n i : ℤ) :
    (sectionsProductTotal C J I).X n ⟶ sectionsProductComplement C J I n i :=
  Pi.lift fun p ↦
    sectionsProductTotal_πOfEq C J I p.1 (n - p.1)
      ((add_comm p.1 (n - p.1)).trans (sub_add_cancel n p.1))

/-- Product-tail stages are antitone in the filtration index. -/
theorem sectionsProductFiltration_monotone
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (n : ℤ) :
    Monotone fun p : ℤᵒᵈ ↦
      kernelSubobject (sectionsProductComplement_π C J I n (OrderDual.ofDual p)) :=
  sorry

/-- Degree `n` of `Tot_π(A)` with the product-tail filtration
`F^i Tot^n = ker(Tot^n ⟶ ∏_{p < i} A^{p, n-p})`. -/
def sectionsProductFiltrationObject
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (n : ℤ) :
    FilteredObject AddCommGrpCat.{max u w} where
  obj := (sectionsProductTotal C J I).X n
  filtration :=
    OrderHom.mk
      (fun p ↦ kernelSubobject (sectionsProductComplement_π C J I n (OrderDual.ofDual p)))
      (sectionsProductFiltration_monotone C J I n)

/-- The total differential preserves every product-tail stage. -/
theorem sectionsProductFiltration_d_preserves
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (a b p : ℤ) :
    ((sectionsProductFiltrationObject C J I b).filtration.stage p).Factors
      (((sectionsProductFiltrationObject C J I a).filtration.stage p).arrow ≫
        (sectionsProductTotal C J I).d a b) :=
  sorry

/-- The product-tail filtered differential in total degree. -/
def sectionsProductFiltration_d
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (a b : ℤ) :
    sectionsProductFiltrationObject C J I a ⟶ sectionsProductFiltrationObject C J I b where
  hom := (sectionsProductTotal C J I).d a b
  preserves := sectionsProductFiltration_d_preserves C J I a b

/-- The product-tail differential vanishes off the cochain shape. -/
theorem sectionsProductFiltration_d_shape
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (a b : ℤ) (hab : ¬ (up ℤ).Rel a b) :
    sectionsProductFiltration_d C J I a b = 0 :=
  sorry

/-- Consecutive product-tail differentials compose to zero. -/
theorem sectionsProductFiltration_d_comp
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (a b c : ℤ) (hab : (up ℤ).Rel a b) (hbc : (up ℤ).Rel b c) :
    sectionsProductFiltration_d C J I a b ≫ sectionsProductFiltration_d C J I b c = 0 :=
  sorry

/-- The filtered complex `Tot_π(A)` with product-tail stages
`F^i Tot^n_π(A) = ∏_{p+q=n, p ≥ i} A^{p,q}`. -/
def sectionsProductFiltration
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)] :
    FilteredComplex AddCommGrpCat.{max u w} where
  X := sectionsProductFiltrationObject C J I
  d := sectionsProductFiltration_d C J I
  shape := sectionsProductFiltration_d_shape C J I
  d_comp_d' := sectionsProductFiltration_d_comp C J I

/-- Forgetting the product-tail filtration recovers `Tot_π(A)`. -/
theorem sectionsProductFiltration_underlying
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)] :
    (sectionsProductFiltration C J I).underlying = sectionsProductTotal C J I :=
  sorry

/-- The filtration stage in total degree `n` is isomorphic to the source product
`∏_{p+q=n, p ≥ i} A^{p,q}`. -/
theorem sectionsProductFiltration_stage_iso
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (n i : ℤ) :
    IsIsomorphic (((sectionsProductFiltration C J I).stage i).X n)
      (sectionsProductStage C J I n i) :=
  sorry

variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [(globalSectionsTotalFunctor C J).Additive]
variable [∀ n : ℕ,
    (Functor.RightDerived.Cochain.toDerived (sectionsStageGamma C J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]
variable [(Functor.RightDerived.Cochain.toDerived (globalSectionsTotalFunctor C J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]

/-- The cochain-level derived natural transformation induced by a map of additive functors. -/
def toDerivedMap
    {F G : Sheaf (topology C J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w}}
    [F.Additive] [G.Additive] (τ : F ⟶ G) :
    Functor.RightDerived.Cochain.toDerived F ⟶ Functor.RightDerived.Cochain.toDerived G :=
  whiskerRight (NatTrans.mapHomologicalComplex τ (up ℤ))
    (DerivedCategory.Q : CochainComplex AddCommGrpCat.{max u w} ℤ ⥤
      DerivedCategory AddCommGrpCat.{max u w})

/-- The total right-derived natural transformation induced by a map of additive functors. -/
def unboundedRightDerivedMap
    {F G : Sheaf (topology C J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w}}
    [F.Additive] [G.Additive]
    [(Functor.RightDerived.Cochain.toDerived F).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]
    [(Functor.RightDerived.Cochain.toDerived G).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]
    (τ : F ⟶ G) :
    Functor.RightDerived.Cochain.functor F ⟶ Functor.RightDerived.Cochain.functor G :=
  Functor.RightDerived.mapNatTrans
    (DerivedCategory.Q : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
      DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))
    (toDerivedMap C J τ)

/-- Nonnegative unbounded first-page target: `H^q` of `RΓ(C_n, (-)_n)`. -/
def unboundedPageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Cochain.functor (sectionsStageGamma C J n) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} q

/-- The Čech differential on nonnegative unbounded first-page functors. -/
def unboundedPageOneDifferentialNonneg (n : ℕ) (q : ℤ) :
    unboundedPageOneFunctorNonneg C J n q ⟶ unboundedPageOneFunctorNonneg C J (n + 1) q :=
  whiskerRight (unboundedRightDerivedMap C J (sectionsStageGamma_d C J n))
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
  sorry

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
        (toNat_succ_of_nonneg hp)).symm ≫
      eqToHom (unboundedPageOneFunctor_eq_of_nonneg C J (p + 1) q (nonneg_succ hp)).symm
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
  sorry

end CategoryTheory.SimplicialSites
