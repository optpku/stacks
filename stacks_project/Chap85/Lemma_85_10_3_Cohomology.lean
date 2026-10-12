/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import stacks_project.Chap85.Lemma_85_10_2_Complex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Module hypercohomology spectral sequences on a morphism diagram of sites

In Situation 85.3.3 case A, the first-filtration spectral sequence of the Čech–Gamma
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

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]

/-- Canonical derived-category structure on `O`-modules on the total site. -/
instance totalModules_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O) :=
  Hom.RingPresentation.moduleHasDerivedCategory (topology C J) O

/-- The component of a morphism of `O`-modules under `Hom(g_n! O_n, -)`. -/
def moduleHomCosimplicialMap {F G : SheafOfModules.{w} O} (f : F ⟶ G) (n : SimplexCategory) :
    (moduleHomCosimplicial C J O F).obj n ⟶ (moduleHomCosimplicial C J O G).obj n :=
  (preadditiveYoneda.map f).app ((lowerShriekUnit C J O).rightOp.obj n)

/-- Naturality of `moduleHomCosimplicialMap` in the simplicial degree. -/
theorem moduleHomCosimplicialMap_naturality {F G : SheafOfModules.{w} O} (f : F ⟶ G)
    {n m : SimplexCategory} (φ : n ⟶ m) :
    (moduleHomCosimplicial C J O F).map φ ≫ moduleHomCosimplicialMap C J O f m =
      moduleHomCosimplicialMap C J O f n ≫ (moduleHomCosimplicial C J O G).map φ :=
  sorry

/-- The natural transformation `Hom(g_•! O_•, F) ⟶ Hom(g_•! O_•, G)` induced by `f`. -/
def moduleHomCosimplicialNatTrans {F G : SheafOfModules.{w} O} (f : F ⟶ G) :
    moduleHomCosimplicial C J O F ⟶ moduleHomCosimplicial C J O G where
  app n := moduleHomCosimplicialMap C J O f n
  naturality _ _ φ := moduleHomCosimplicialMap_naturality C J O f φ

/-- Identity morphisms act as the identity on `moduleHomCosimplicial`. -/
theorem moduleHomCosimplicialNatTrans_id (F : SheafOfModules.{w} O) :
    moduleHomCosimplicialNatTrans C J O (𝟙 F) = 𝟙 (moduleHomCosimplicial C J O F) :=
  sorry

/-- `moduleHomCosimplicialNatTrans` preserves composition. -/
theorem moduleHomCosimplicialNatTrans_comp {F G H : SheafOfModules.{w} O}
    (f : F ⟶ G) (g : G ⟶ H) :
    moduleHomCosimplicialNatTrans C J O (f ≫ g) =
      moduleHomCosimplicialNatTrans C J O f ≫ moduleHomCosimplicialNatTrans C J O g :=
  sorry

/-- The functor sending an `O`-module `F` to the cosimplicial object `n ↦ Hom(g_n! O_n, F)`. -/
def moduleHomCosimplicialFunctor :
    SheafOfModules.{w} O ⥤ CosimplicialObject AddCommGrpCat.{max u w} where
  obj F := moduleHomCosimplicial C J O F
  map f := moduleHomCosimplicialNatTrans C J O f
  map_id := moduleHomCosimplicialNatTrans_id C J O
  map_comp := moduleHomCosimplicialNatTrans_comp C J O

/-- The functor sending an `O`-module to the unaugmented Čech cochain `Γ(C_•, F_•)`. -/
def moduleCechComplexFunctor :
    SheafOfModules.{w} O ⥤ CochainComplex AddCommGrpCat.{max u w} ℕ :=
  moduleHomCosimplicialFunctor C J O ⋙ alternatingCofaceMapComplex _

/-- Degree-`p` term of the unaugmented Čech cochain, as a functor of the `O`-module. -/
def componentSectionsFunctor (p : ℕ) :
    SheafOfModules.{w} O ⥤ AddCommGrpCat.{max u w} :=
  moduleCechComplexFunctor C J O ⋙ HomologicalComplex.eval _ _ p

/-- Global sections of an `O`-module on the total site, as `Hom(O, -)`. -/
def totalSectionsFunctor :
    SheafOfModules.{w} O ⥤ AddCommGrpCat.{max u w} :=
  preadditiveYoneda ⋙
    (evaluation (SheafOfModules.{w} O)ᵒᵖ AddCommGrpCat.{max u w}).obj
      (op (SheafOfModules.unit O))

/-- `componentSectionsFunctor` is additive. -/
instance componentSectionsFunctor_additive (p : ℕ) :
    (componentSectionsFunctor C J O p).Additive :=
  sorry

/-- `totalSectionsFunctor` is additive. -/
instance totalSectionsFunctor_additive :
    (totalSectionsFunctor C J O).Additive :=
  sorry

/-- `moduleCechComplexFunctor` preserves zero morphisms. -/
instance moduleCechComplexFunctor_additive :
    (moduleCechComplexFunctor C J O).Additive :=
  sorry

/-- Naturality of the Čech differential in the `O`-module. -/
theorem componentSections_d1_naturality (p : ℕ) {F G : SheafOfModules.{w} O} (f : F ⟶ G) :
    (componentSectionsFunctor C J O p).map f ≫
        ((moduleCechComplexFunctor C J O).obj G).d p (p + 1) =
      ((moduleCechComplexFunctor C J O).obj F).d p (p + 1) ≫
        (componentSectionsFunctor C J O (p + 1)).map f :=
  sorry

/-- The horizontal Čech differential `Γ(C_p, F_p) ⟶ Γ(C_{p+1}, F_{p+1})`, as a natural
transformation in the `O`-module `F`. -/
def componentSections_d1 (p : ℕ) :
    componentSectionsFunctor C J O p ⟶ componentSectionsFunctor C J O (p + 1) where
  app F := ((moduleCechComplexFunctor C J O).obj F).d p (p + 1)
  naturality _ _ f := componentSections_d1_naturality C J O p f

/-- The Čech–Gamma bicomplex of a cochain complex of `O`-modules, with
`A^{p,q} = Hom(g_p! O_p, I^q)` for `p ≥ 0` and `0` for `p < 0`. -/
def moduleGammaBicomplex (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ) :=
  ((moduleCechComplexFunctor C J O ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{max u w}).mapHomologicalComplex
    (up ℤ)).obj I

/-- Evaluating `moduleGammaBicomplex` in nonnegative horizontal degree recovers the Čech
cochain of the corresponding term of `I`. -/
theorem moduleGammaBicomplex_X (I : CochainComplex (SheafOfModules.{w} O) ℤ)
    (p : ℕ) (q : ℤ) :
    ((moduleGammaBicomplex C J O I).X (Int.ofNat p)).X q =
      ((moduleCechComplexFunctor C J O).obj (I.X q)).X p :=
  sorry

/-- Consecutive horizontal differentials of `moduleGammaBicomplex` compose to zero. -/
theorem moduleGammaBicomplex_d_comp_zero
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) (p q : ℤ) :
    ((moduleGammaBicomplex C J O I).d p (p + 1)).f q ≫
      ((moduleGammaBicomplex C J O I).d (p + 1) (p + 2)).f q = 0 :=
  sorry

/-- Negative Čech columns of `moduleGammaBicomplex` vanish. -/
theorem moduleGammaBicomplex_isZero_of_neg
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) {p : ℤ} (hp : p < 0) :
    IsZero ((moduleGammaBicomplex C J O I).X p) :=
  sorry

variable [∀ p : ℕ,
    (componentSectionsFunctor C J O p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]
variable [(totalSectionsFunctor C J O).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]

/-- Stage hypercohomology `H^q(C_p, K_p)`, as the cohomology of the bounded-below
right-derived functor of `Hom(g_p! O_p, -)`. -/
def componentHypercohomologyFunctor (p : ℕ) (q : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Bounded.functor (componentSectionsFunctor C J O p) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q

/-- Evaluating stage hypercohomology recovers the homology of the bounded-below derived
functor of `Hom(g_p! O_p, -)`. -/
theorem componentHypercohomologyFunctor_obj (p : ℕ) (q : ℤ)
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    (componentHypercohomologyFunctor C J O p q).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q).obj
        ((Functor.RightDerived.Bounded.functor
          (componentSectionsFunctor C J O p)).obj K) :=
  sorry

/-- Stage hypercohomology acts on morphisms by the homology of the bounded-below derived
functor of `Hom(g_p! O_p, -)`. -/
theorem componentHypercohomologyFunctor_map (p : ℕ) (q : ℤ)
    {K L : DerivedCategory.Plus (SheafOfModules.{w} O)} (φ : K ⟶ L) :
    (componentHypercohomologyFunctor C J O p q).map φ =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q).map
        ((Functor.RightDerived.Bounded.functor
          (componentSectionsFunctor C J O p)).map φ) :=
  sorry

/-- Total hypercohomology `H^n(C_total, K)`, as the cohomology of the bounded-below
right-derived functor of `Hom(O, -)`. -/
def totalHypercohomologyFunctor (n : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Bounded.functor (totalSectionsFunctor C J O) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n

/-- Evaluating total hypercohomology recovers the homology of the bounded-below derived
functor of `Hom(O, -)`. -/
theorem totalHypercohomologyFunctor_obj (n : ℤ)
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    (totalHypercohomologyFunctor C J O n).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((Functor.RightDerived.Bounded.functor (totalSectionsFunctor C J O)).obj K) :=
  sorry

/-- Total hypercohomology acts on morphisms by the homology of the bounded-below derived
functor of `Hom(O, -)`. -/
theorem totalHypercohomologyFunctor_map (n : ℤ)
    {K L : DerivedCategory.Plus (SheafOfModules.{w} O)} (φ : K ⟶ L) :
    (totalHypercohomologyFunctor C J O n).map φ =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n).map
        ((Functor.RightDerived.Bounded.functor (totalSectionsFunctor C J O)).map φ) :=
  sorry

/-- The Čech differential on nonnegative first-page functors. -/
def componentHypercohomology_d1 (p : ℕ) (q : ℤ) :
    componentHypercohomologyFunctor C J O p q ⟶
      componentHypercohomologyFunctor C J O (p + 1) q :=
  whiskerRight
    (Functor.RightDerived.Bounded.map (componentSections_d1 C J O p))
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q)

/-- First-page target `K ↦ H^q(C_p, K_p)`, vanishing for `p < 0`. -/
def modulePageOneFunctor (p q : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ AddCommGrpCat.{max u w} :=
  if 0 ≤ p then componentHypercohomologyFunctor C J O p.toNat q else
    (Functor.const (DerivedCategory.Plus (SheafOfModules.{w} O))).obj
      (0 : AddCommGrpCat.{max u w})

/-- Nonnegative bidegrees of `modulePageOneFunctor` recover stage hypercohomology. -/
theorem modulePageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    modulePageOneFunctor C J O p q =
      componentHypercohomologyFunctor C J O p.toNat q :=
  sorry

/-- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
def modulePageOneDifferential (p q : ℤ) :
    modulePageOneFunctor C J O p q ⟶ modulePageOneFunctor C J O (p + 1) q :=
  if hp : 0 ≤ p then
    eqToHom (if_pos hp) ≫
      componentHypercohomology_d1 C J O p.toNat q ≫
      eqToHom (congrArg (componentHypercohomologyFunctor C J O · q)
        (Int.toNat_add_nat hp 1)).symm ≫
      eqToHom (if_pos (Int.add_nonneg hp zero_le_one)).symm
  else
    (0 : modulePageOneFunctor C J O p q ⟶ modulePageOneFunctor C J O (p + 1) q)

/-- First-page groups in negative Čech degree vanish. -/
theorem modulePageOneFunctor_neg
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) {p : ℤ} (hp : p < 0)
    (q : ℤ) :
    IsZero ((modulePageOneFunctor C J O p q).obj K) :=
  sorry


end CategoryTheory.SimplicialSites
