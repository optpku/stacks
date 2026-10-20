module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Cech

/-!
# Module hypercohomology spectral sequences on a morphism diagram of sites

The first-filtration spectral sequence of the Čech–Gamma
bicomplex of a bounded-below complex of `O`-modules. The first page is identified with
stage hypercohomology `H^q(C_p, K_p)`, realized as the right-derived functor of
`Hom(g_p! O_p, -)`, and the abutment is `H^{p+q}(C_total, K)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory RingedSite ZeroObject
open FilteredComplex.SpectralSequence.Realization
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.ModuleCohomology

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
variable [UnivLE.{max u v, w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Canonical derived-category structure on `O`-modules on the total site. -/
instance totalModules_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O) :=
  HasDerivedCategory.standard (SheafOfModules.{w} O)

/-- The functor sending an `O`-module to the cosimplicial abelian group
`n ↦ Hom(g_n! O_n, -)`. -/
def moduleHomCosimplicialFunctor :
    SheafOfModules.{w} O ⥤ CosimplicialObject AddCommGrpCat.{max u w} :=
  preadditiveYoneda ⋙
    (Functor.whiskeringLeft SimplexCategory (SheafOfModules.{w} O)ᵒᵖ
      AddCommGrpCat.{max u w}).obj ((lowerShriekUnit C J O).rightOp)

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

/-- The module Čech cochain functor is additive. -/
instance moduleCechComplexFunctor_additive :
    (moduleCechComplexFunctor C J O).Additive :=
  sorry

/-- The horizontal Čech differential on stage sections, naturally in the module. -/
def componentSections_d1 (p : ℕ) :
    componentSectionsFunctor C J O p ⟶ componentSectionsFunctor C J O (p + 1) :=
  whiskerLeft (moduleCechComplexFunctor C J O)
    (HomologicalComplex.dNatTrans _ _ p (p + 1))

/-- The Čech–Gamma bicomplex of a cochain complex of `O`-modules, with
`A^{p,q} = Hom(g_p! O_p, I^q)` for `p ≥ 0` and `0` for `p < 0`. -/
def moduleGammaBicomplex (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ) :=
  HomologicalComplex₂.flip (((moduleCechComplexFunctor C J O ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{max u w}).mapHomologicalComplex
    (up ℤ)).obj I)

/-- Evaluating `moduleGammaBicomplex` in nonnegative horizontal degree recovers the Čech
cochain of the corresponding term of `I`. -/
theorem moduleGammaBicomplex_X (I : CochainComplex (SheafOfModules.{w} O) ℤ)
    (p : ℕ) (q : ℤ) :
    ((moduleGammaBicomplex C J O I).X (Int.ofNat p)).X q =
      ((moduleCechComplexFunctor C J O).obj (I.X q)).X p :=
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


/-- Every bounded-below derived module on the total simplicial site admits a convergent
spectral sequence with stage hypercohomology on the first page and the canonical
alternating-coface differential. -/
theorem exists_spectralSequence
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    ∃ (S : WithAbutment (fun n ↦ totalHypercohomologyFunctor C J O n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅ (modulePageOneFunctor C J O p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (modulePageOneDifferential C J O p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- The stage-hypercohomology spectral sequences can be chosen simultaneously for all
bounded-below derived modules, with natural first-page comparisons and maps preserving
identities and composition on spectral sequences. -/
theorem spectralSequence_functorial :
    ∃ (S : ∀ K : DerivedCategory.Plus (SheafOfModules.{w} O),
        WithAbutment (fun n ↦ totalHypercohomologyFunctor C J O n) K)
      (pageOneIso : ∀ (K : DerivedCategory.Plus (SheafOfModules.{w} O)) (p q : ℤ),
        ((S K).sequence.page 1).X (p, q) ≅ (modulePageOneFunctor C J O p q).obj K)
      (m : ∀ {K L : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : K ⟶ L),
        WithAbutment.Map (fun n ↦ totalHypercohomologyFunctor C J O n) f (S K) (S L)),
      (∀ (K : DerivedCategory.Plus (SheafOfModules.{w} O)) (p q : ℤ),
        (pageOneIso K p q).hom ≫ (modulePageOneDifferential C J O p q).app K =
          ((S K).sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso K (p + 1) q).hom) ∧
      (∀ {K L : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : K ⟶ L) (p q : ℤ),
        ((m f).sequenceMap.hom 1).f (p, q) ≫ (pageOneIso L p q).hom =
          (pageOneIso K p q).hom ≫ (modulePageOneFunctor C J O p q).map f) ∧
      (∀ K : DerivedCategory.Plus (SheafOfModules.{w} O),
        (m (𝟙 K)).sequenceMap = 𝟙 (S K).sequence) ∧
      (∀ {K L M : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : K ⟶ L) (g : L ⟶ M),
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap) :=
  sorry

end CategoryTheory.SimplicialSites.ModuleCohomology
