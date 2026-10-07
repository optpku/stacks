module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import stacks_project.Chap85.Lemma_85_10_2_Fiberwise
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Module hypercohomology spectral sequences on a fiberwise simplicial site

In Situation 85.3.3 case B, the first-filtration spectral sequence of the Čech–Gamma
bicomplex of a bounded-below complex of `O`-modules. The first page is identified with
stage hypercohomology `H^q(C_p, K_p)`, realized as the right-derived functor of
`Hom(g_p! O_p, -)`, and the abutment is `H^{p+q}(C_total, K)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory RingedSite ZeroObject
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]

/-- Canonical derived-category structure on `O`-modules on the case B total site. -/
instance fiberTotalModules_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O) :=
  Hom.RingPresentation.moduleHasDerivedCategory (topology F J) O

/-- The component of a morphism of `O`-modules under `Hom(g_n! O_n, -)` in case B. -/
def fiberModuleHomCosimplicialMap {M N : SheafOfModules.{w} O} (f : M ⟶ N)
    (n : SimplexCategory) :
    (fiberModuleHomCosimplicial F J O M).obj n ⟶
      (fiberModuleHomCosimplicial F J O N).obj n :=
  (preadditiveYoneda.map f).app ((fiberLowerShriekUnit F J O).rightOp.obj n)

/-- Naturality of `fiberModuleHomCosimplicialMap` in the simplicial degree. -/
theorem fiberModuleHomCosimplicialMap_naturality {M N : SheafOfModules.{w} O} (f : M ⟶ N)
    {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberModuleHomCosimplicial F J O M).map φ ≫ fiberModuleHomCosimplicialMap F J O f m =
      fiberModuleHomCosimplicialMap F J O f n ≫
        (fiberModuleHomCosimplicial F J O N).map φ :=
  sorry

/-- The natural transformation `Hom(g_•! O_•, M) ⟶ Hom(g_•! O_•, N)` induced by `f`. -/
def fiberModuleHomCosimplicialNatTrans {M N : SheafOfModules.{w} O} (f : M ⟶ N) :
    fiberModuleHomCosimplicial F J O M ⟶ fiberModuleHomCosimplicial F J O N where
  app n := fiberModuleHomCosimplicialMap F J O f n
  naturality _ _ φ := fiberModuleHomCosimplicialMap_naturality F J O f φ

/-- Identity morphisms act as the identity on `fiberModuleHomCosimplicial`. -/
theorem fiberModuleHomCosimplicialNatTrans_id (M : SheafOfModules.{w} O) :
    fiberModuleHomCosimplicialNatTrans F J O (𝟙 M) =
      𝟙 (fiberModuleHomCosimplicial F J O M) :=
  sorry

/-- `fiberModuleHomCosimplicialNatTrans` preserves composition. -/
theorem fiberModuleHomCosimplicialNatTrans_comp {M N P : SheafOfModules.{w} O}
    (f : M ⟶ N) (g : N ⟶ P) :
    fiberModuleHomCosimplicialNatTrans F J O (f ≫ g) =
      fiberModuleHomCosimplicialNatTrans F J O f ≫
        fiberModuleHomCosimplicialNatTrans F J O g :=
  sorry

/-- The functor sending an `O`-module `M` to `n ↦ Hom(g_n! O_n, M)` in case B. -/
def fiberModuleHomCosimplicialFunctor :
    SheafOfModules.{w} O ⥤ CosimplicialObject AddCommGrpCat.{max u w} where
  obj M := fiberModuleHomCosimplicial F J O M
  map f := fiberModuleHomCosimplicialNatTrans F J O f
  map_id := fiberModuleHomCosimplicialNatTrans_id F J O
  map_comp := fiberModuleHomCosimplicialNatTrans_comp F J O

/-- The functor sending an `O`-module to the unaugmented case B Čech cochain. -/
def fiberModuleCechComplexFunctor :
    SheafOfModules.{w} O ⥤ CochainComplex AddCommGrpCat.{max u w} ℕ :=
  fiberModuleHomCosimplicialFunctor F J O ⋙ alternatingCofaceMapComplex _

/-- Degree-`p` term of the unaugmented case B Čech cochain, as a functor of the module. -/
def fiberComponentSectionsFunctor (p : ℕ) :
    SheafOfModules.{w} O ⥤ AddCommGrpCat.{max u w} :=
  fiberModuleCechComplexFunctor F J O ⋙ HomologicalComplex.eval _ _ p

/-- Global sections of an `O`-module on the case B total site, as `Hom(O, -)`. -/
def fiberTotalSectionsFunctor :
    SheafOfModules.{w} O ⥤ AddCommGrpCat.{max u w} :=
  preadditiveYoneda ⋙
    (evaluation (SheafOfModules.{w} O)ᵒᵖ AddCommGrpCat.{max u w}).obj
      (op (SheafOfModules.unit O))

/-- `fiberComponentSectionsFunctor` is additive. -/
instance fiberComponentSectionsFunctor_additive (p : ℕ) :
    (fiberComponentSectionsFunctor F J O p).Additive :=
  sorry

/-- `fiberTotalSectionsFunctor` is additive. -/
instance fiberTotalSectionsFunctor_additive :
    (fiberTotalSectionsFunctor F J O).Additive :=
  sorry

/-- `fiberModuleCechComplexFunctor` is additive. -/
instance fiberModuleCechComplexFunctor_additive :
    (fiberModuleCechComplexFunctor F J O).Additive :=
  sorry

/-- Naturality of the case B Čech differential in the `O`-module. -/
theorem fiberComponentSections_d1_naturality (p : ℕ)
    {M N : SheafOfModules.{w} O} (f : M ⟶ N) :
    (fiberComponentSectionsFunctor F J O p).map f ≫
        ((fiberModuleCechComplexFunctor F J O).obj N).d p (p + 1) =
      ((fiberModuleCechComplexFunctor F J O).obj M).d p (p + 1) ≫
        (fiberComponentSectionsFunctor F J O (p + 1)).map f :=
  sorry

/-- The horizontal Čech differential in case B, as a natural transformation in the module. -/
def fiberComponentSections_d1 (p : ℕ) :
    fiberComponentSectionsFunctor F J O p ⟶
      fiberComponentSectionsFunctor F J O (p + 1) where
  app M := ((fiberModuleCechComplexFunctor F J O).obj M).d p (p + 1)
  naturality _ _ f := fiberComponentSections_d1_naturality F J O p f

/-- The case B Čech–Gamma bicomplex of a cochain complex of `O`-modules. -/
def fiberModuleGammaBicomplex (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ) :=
  ((fiberModuleCechComplexFunctor F J O ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{max u w}).mapHomologicalComplex
    (up ℤ)).obj I

/-- Evaluating `fiberModuleGammaBicomplex` in nonnegative horizontal degree recovers the
Čech cochain of the corresponding term of `I`. -/
theorem fiberModuleGammaBicomplex_X (I : CochainComplex (SheafOfModules.{w} O) ℤ)
    (p : ℕ) (q : ℤ) :
    ((fiberModuleGammaBicomplex F J O I).X (Int.ofNat p)).X q =
      ((fiberModuleCechComplexFunctor F J O).obj (I.X q)).X p :=
  sorry

/-- Consecutive horizontal differentials of `fiberModuleGammaBicomplex` compose to zero. -/
theorem fiberModuleGammaBicomplex_d_comp_zero
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) (p q : ℤ) :
    ((fiberModuleGammaBicomplex F J O I).d p (p + 1)).f q ≫
      ((fiberModuleGammaBicomplex F J O I).d (p + 1) (p + 2)).f q = 0 :=
  sorry

/-- Negative Čech columns of `fiberModuleGammaBicomplex` vanish. -/
theorem fiberModuleGammaBicomplex_isZero_of_neg
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) {p : ℤ} (hp : p < 0) :
    IsZero ((fiberModuleGammaBicomplex F J O I).X p) :=
  sorry

variable [∀ p : ℕ,
    (fiberComponentSectionsFunctor F J O p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]
variable [(fiberTotalSectionsFunctor F J O).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]

/-- Stage hypercohomology `H^q(C_p, K_p)` in case B. -/
def fiberHypercohomologyFunctor (p : ℕ) (q : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Bounded.functor (fiberComponentSectionsFunctor F J O p) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q

/-- Evaluating case B stage hypercohomology recovers the homology of the bounded-below
derived functor of `Hom(g_p! O_p, -)`. -/
theorem fiberHypercohomologyFunctor_obj (p : ℕ) (q : ℤ)
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    (fiberHypercohomologyFunctor F J O p q).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q).obj
        ((Functor.RightDerived.Bounded.functor
          (fiberComponentSectionsFunctor F J O p)).obj K) :=
  sorry

/-- Case B stage hypercohomology acts on morphisms by the homology of the bounded-below
derived functor of `Hom(g_p! O_p, -)`. -/
theorem fiberHypercohomologyFunctor_map (p : ℕ) (q : ℤ)
    {K L : DerivedCategory.Plus (SheafOfModules.{w} O)} (φ : K ⟶ L) :
    (fiberHypercohomologyFunctor F J O p q).map φ =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q).map
        ((Functor.RightDerived.Bounded.functor
          (fiberComponentSectionsFunctor F J O p)).map φ) :=
  sorry

/-- Total hypercohomology `H^n(C_total, K)` in case B. -/
def fiberTotalHypercohomologyFunctor (n : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Bounded.functor (fiberTotalSectionsFunctor F J O) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n

/-- Evaluating case B total hypercohomology recovers the homology of the bounded-below
derived functor of `Hom(O, -)`. -/
theorem fiberTotalHypercohomologyFunctor_obj (n : ℤ)
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    (fiberTotalHypercohomologyFunctor F J O n).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((Functor.RightDerived.Bounded.functor
          (fiberTotalSectionsFunctor F J O)).obj K) :=
  sorry

/-- Case B total hypercohomology acts on morphisms by the homology of the bounded-below
derived functor of `Hom(O, -)`. -/
theorem fiberTotalHypercohomologyFunctor_map (n : ℤ)
    {K L : DerivedCategory.Plus (SheafOfModules.{w} O)} (φ : K ⟶ L) :
    (fiberTotalHypercohomologyFunctor F J O n).map φ =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n).map
        ((Functor.RightDerived.Bounded.functor
          (fiberTotalSectionsFunctor F J O)).map φ) :=
  sorry

/-- The Čech differential on nonnegative first-page functors in case B. -/
def fiberHypercohomology_d1 (p : ℕ) (q : ℤ) :
    fiberHypercohomologyFunctor F J O p q ⟶
      fiberHypercohomologyFunctor F J O (p + 1) q :=
  whiskerRight
    (Functor.RightDerived.Bounded.map (fiberComponentSections_d1 F J O p))
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q)

/-- First-page target `K ↦ H^q(C_p, K_p)` in case B, vanishing for `p < 0`. -/
def fiberPageOneFunctor (p q : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ AddCommGrpCat.{max u w} :=
  if 0 ≤ p then fiberHypercohomologyFunctor F J O p.toNat q else
    (Functor.const (DerivedCategory.Plus (SheafOfModules.{w} O))).obj
      (0 : AddCommGrpCat.{max u w})

/-- Nonnegative bidegrees of `fiberPageOneFunctor` recover stage hypercohomology. -/
theorem fiberPageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    fiberPageOneFunctor F J O p q =
      fiberHypercohomologyFunctor F J O p.toNat q :=
  sorry

/-- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}` in case B. -/
def fiberPageOneDifferential (p q : ℤ) :
    fiberPageOneFunctor F J O p q ⟶ fiberPageOneFunctor F J O (p + 1) q :=
  if hp : 0 ≤ p then
    eqToHom (if_pos hp) ≫
      fiberHypercohomology_d1 F J O p.toNat q ≫
      eqToHom (congrArg (fiberHypercohomologyFunctor F J O · q)
        (Int.toNat_add_nat hp 1)).symm ≫
      eqToHom (if_pos (Int.add_nonneg hp zero_le_one)).symm
  else
    (0 : fiberPageOneFunctor F J O p q ⟶ fiberPageOneFunctor F J O (p + 1) q)

/-- First-page groups in negative Čech degree vanish in case B. -/
theorem fiberPageOneFunctor_neg
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) {p : ℤ} (hp : p < 0)
    (q : ℤ) :
    IsZero ((fiberPageOneFunctor F J O p q).obj K) :=
  sorry

end CategoryTheory.Grothendieck
