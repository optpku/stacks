/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
public import stacks_project.Chap85.Lemma_85_8_3_Fiberwise

/-!
# Product total of the fiberwise Čech–injective bicomplex

In Situation 85.3.3 case B, the product total `Tot_π(A)` of
`A^{p,q} = Γ(C_p, I^q_p)` on the total fiberwise site, its product-tail
filtration, and the unbounded first-page functors of stagewise global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory ZeroObject
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

/-- The product total `Tot_π(A)` of the fiberwise Čech–injective bicomplex. -/
def fiberSectionsProductTotal
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)] :
    CochainComplex AddCommGrpCat.{max u w} ℤ :=
  HomologicalComplex₂.ProductTotal.complex (fiberSectionsBicomplex F J I)

/-- Antidiagonal projection `Tot^{p+q}_π(A) ⟶ A^{p,q}`. -/
def fiberSectionsProductTotal_π
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (p q : ℤ) :
    (fiberSectionsProductTotal F J I).X (p + q) ⟶
      ((fiberSectionsBicomplex F J I).X p).X q :=
  HomologicalComplex₂.ProductTotal.π (fiberSectionsBicomplex F J I) p q

/-- Antidiagonal projection at an identified total degree. -/
def fiberSectionsProductTotal_πOfEq
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (p q : ℤ) {n : ℤ} (h : p + q = n) :
    (fiberSectionsProductTotal F J I).X n ⟶ ((fiberSectionsBicomplex F J I).X p).X q :=
  HomologicalComplex₂.ProductTotal.πOfEq (fiberSectionsBicomplex F J I) p q h

/-- The source product `∏_{p+q=n, p ≥ i} A^{p,q}`. -/
def fiberSectionsProductStage
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    (n i : ℤ) :
    AddCommGrpCat.{max u w} :=
  ∏ᶜ fun p : {p : ℤ // i ≤ p} ↦ ((fiberSectionsBicomplex F J I).X p.1).X (n - p.1)

/-- Projection from the source product onto a retained bidegree. -/
def fiberSectionsProductStage_π
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    (n i : ℤ) (p : {p : ℤ // i ≤ p}) :
    fiberSectionsProductStage F J I n i ⟶
      ((fiberSectionsBicomplex F J I).X p.1).X (n - p.1) :=
  Pi.π (fun q : {q : ℤ // i ≤ q} ↦ ((fiberSectionsBicomplex F J I).X q.1).X (n - q.1)) p

/-- The complementary product of discarded antidiagonal summands `p < i`. -/
def fiberSectionsProductComplement
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    (n i : ℤ) :
    AddCommGrpCat.{max u w} :=
  ∏ᶜ fun p : {p : ℤ // p < i} ↦ ((fiberSectionsBicomplex F J I).X p.1).X (n - p.1)

/-- The canonical map `Tot^n_π(A) ⟶ ∏_{p+q=n, p < i} A^{p,q}`. -/
def fiberSectionsProductComplement_π
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (n i : ℤ) :
    (fiberSectionsProductTotal F J I).X n ⟶ fiberSectionsProductComplement F J I n i :=
  Pi.lift fun p ↦
    fiberSectionsProductTotal_πOfEq F J I p.1 (n - p.1)
      ((add_comm p.1 (n - p.1)).trans (sub_add_cancel n p.1))

/-- Product-tail stages are antitone in the filtration index. -/
theorem fiberSectionsProductFiltration_monotone
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (n : ℤ) :
    Monotone fun p : ℤᵒᵈ ↦
      kernelSubobject (fiberSectionsProductComplement_π F J I n (OrderDual.ofDual p)) :=
  sorry

/-- Degree `n` of `Tot_π(A)` with the product-tail filtration. -/
def fiberSectionsProductFiltrationObject
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (n : ℤ) :
    FilteredObject AddCommGrpCat.{max u w} where
  obj := (fiberSectionsProductTotal F J I).X n
  filtration :=
    OrderHom.mk
      (fun p ↦ kernelSubobject (fiberSectionsProductComplement_π F J I n (OrderDual.ofDual p)))
      (fiberSectionsProductFiltration_monotone F J I n)

/-- The total differential preserves every product-tail stage. -/
theorem fiberSectionsProductFiltration_d_preserves
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (a b p : ℤ) :
    ((fiberSectionsProductFiltrationObject F J I b).filtration.stage p).Factors
      (((fiberSectionsProductFiltrationObject F J I a).filtration.stage p).arrow ≫
        (fiberSectionsProductTotal F J I).d a b) :=
  sorry

/-- The product-tail filtered differential in total degree. -/
def fiberSectionsProductFiltration_d
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (a b : ℤ) :
    fiberSectionsProductFiltrationObject F J I a ⟶
      fiberSectionsProductFiltrationObject F J I b where
  hom := (fiberSectionsProductTotal F J I).d a b
  preserves := fiberSectionsProductFiltration_d_preserves F J I a b

/-- The product-tail differential vanishes off the cochain shape. -/
theorem fiberSectionsProductFiltration_d_shape
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (a b : ℤ) (hab : ¬ (up ℤ).Rel a b) :
    fiberSectionsProductFiltration_d F J I a b = 0 :=
  sorry

/-- Consecutive product-tail differentials compose to zero. -/
theorem fiberSectionsProductFiltration_d_comp
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (a b c : ℤ) (hab : (up ℤ).Rel a b) (hbc : (up ℤ).Rel b c) :
    fiberSectionsProductFiltration_d F J I a b ≫
      fiberSectionsProductFiltration_d F J I b c = 0 :=
  sorry

/-- The filtered complex `Tot_π(A)` with product-tail stages. -/
def fiberSectionsProductFiltration
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)] :
    FilteredComplex AddCommGrpCat.{max u w} where
  X := fiberSectionsProductFiltrationObject F J I
  d := fiberSectionsProductFiltration_d F J I
  shape := fiberSectionsProductFiltration_d_shape F J I
  d_comp_d' := fiberSectionsProductFiltration_d_comp F J I

/-- Forgetting the product-tail filtration recovers `Tot_π(A)`. -/
theorem fiberSectionsProductFiltration_underlying
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)] :
    (fiberSectionsProductFiltration F J I).underlying = fiberSectionsProductTotal F J I :=
  sorry

/-- The filtration stage in total degree `n` is isomorphic to the source product. -/
theorem fiberSectionsProductFiltration_stage_iso
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (n i : ℤ) :
    IsIsomorphic (((fiberSectionsProductFiltration F J I).stage i).X n)
      (fiberSectionsProductStage F J I n i) :=
  sorry

variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [(fiberSectionsTotalFunctor F J).Additive]
variable [∀ n : ℕ,
    (Functor.RightDerived.Cochain.toDerived (fiberSectionsStageGamma F J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]
variable [(Functor.RightDerived.Cochain.toDerived (fiberSectionsTotalFunctor F J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]

/-- The cochain-level derived natural transformation induced by a map of additive functors. -/
def fiberToDerivedMap
    {G H : Sheaf (topology F J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w}}
    [G.Additive] [H.Additive] (τ : G ⟶ H) :
    Functor.RightDerived.Cochain.toDerived G ⟶ Functor.RightDerived.Cochain.toDerived H :=
  whiskerRight (NatTrans.mapHomologicalComplex τ (up ℤ))
    (DerivedCategory.Q : CochainComplex AddCommGrpCat.{max u w} ℤ ⥤
      DerivedCategory AddCommGrpCat.{max u w})

/-- The total right-derived natural transformation induced by a map of additive functors. -/
def fiberUnboundedRightDerivedMap
    {G H : Sheaf (topology F J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w}}
    [G.Additive] [H.Additive]
    [(Functor.RightDerived.Cochain.toDerived G).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]
    [(Functor.RightDerived.Cochain.toDerived H).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]
    (τ : G ⟶ H) :
    Functor.RightDerived.Cochain.functor G ⟶ Functor.RightDerived.Cochain.functor H :=
  Functor.RightDerived.mapNatTrans
    (DerivedCategory.Q : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
      DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))
    (fiberToDerivedMap F J τ)

/-- Nonnegative unbounded first-page target: `H^q` of `RΓ(C_n, (-)_n)`. -/
def fiberUnboundedPageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Cochain.functor (fiberSectionsStageGamma F J n) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{max u w} q

/-- The Čech differential on nonnegative unbounded first-page functors. -/
def fiberUnboundedPageOneDifferentialNonneg (n : ℕ) (q : ℤ) :
    fiberUnboundedPageOneFunctorNonneg F J n q ⟶
      fiberUnboundedPageOneFunctorNonneg F J (n + 1) q :=
  whiskerRight (fiberUnboundedRightDerivedMap F J (fiberSectionsStageGamma_d F J n))
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
  sorry

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
        (fiber_toNat_succ_of_nonneg hp)).symm ≫
      eqToHom (fiberUnboundedPageOneFunctor_eq_of_nonneg F J (p + 1) q
        (fiber_nonneg_succ hp)).symm
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
  sorry

end CategoryTheory.Grothendieck
