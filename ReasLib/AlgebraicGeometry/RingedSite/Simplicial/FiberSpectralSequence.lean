module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCech

/-!
# Module hypercohomology spectral sequences on a fiberwise simplicial site

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

namespace CategoryTheory.Grothendieck.ModuleCohomology

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

/-- Canonical derived-category structure on `O`-modules on the fiberwise total site. -/
instance fiberTotalModules_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O) :=
  HasDerivedCategory.standard (SheafOfModules.{w} O)

/-- The functor sending an `O`-module to the cosimplicial abelian group
`n ↦ Hom(g_n! O_n, -)`. -/
def fiberModuleHomCosimplicialFunctor :
    SheafOfModules.{w} O ⥤ CosimplicialObject AddCommGrpCat.{max u w} :=
  preadditiveYoneda ⋙
    (Functor.whiskeringLeft SimplexCategory (SheafOfModules.{w} O)ᵒᵖ
      AddCommGrpCat.{max u w}).obj ((fiberLowerShriekUnit F J O).rightOp)

/-- The functor sending an `O`-module to the unaugmented fiberwise Čech cochain. -/
def fiberModuleCechComplexFunctor :
    SheafOfModules.{w} O ⥤ CochainComplex AddCommGrpCat.{max u w} ℕ :=
  fiberModuleHomCosimplicialFunctor F J O ⋙ alternatingCofaceMapComplex _

/-- Degree-`p` term of the unaugmented fiberwise Čech cochain, as a functor of the module. -/
def fiberComponentSectionsFunctor (p : ℕ) :
    SheafOfModules.{w} O ⥤ AddCommGrpCat.{max u w} :=
  fiberModuleCechComplexFunctor F J O ⋙ HomologicalComplex.eval _ _ p

/-- Global sections of an `O`-module on the fiberwise total site, as `Hom(O, -)`. -/
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

/-- The horizontal Čech differential on stage sections, naturally in the module. -/
def fiberComponentSections_d1 (p : ℕ) :
    fiberComponentSectionsFunctor F J O p ⟶ fiberComponentSectionsFunctor F J O (p + 1) :=
  whiskerLeft (fiberModuleCechComplexFunctor F J O)
    (HomologicalComplex.dNatTrans _ _ p (p + 1))

/-- The fiberwise Čech–Gamma bicomplex of a cochain complex of `O`-modules. -/
def fiberModuleGammaBicomplex (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ) :=
  HomologicalComplex₂.flip (((fiberModuleCechComplexFunctor F J O ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{max u w}).mapHomologicalComplex
    (up ℤ)).obj I)

/-- Evaluating `fiberModuleGammaBicomplex` in nonnegative horizontal degree recovers the
Čech cochain of the corresponding term of `I`. -/
theorem fiberModuleGammaBicomplex_X (I : CochainComplex (SheafOfModules.{w} O) ℤ)
    (p : ℕ) (q : ℤ) :
    ((fiberModuleGammaBicomplex F J O I).X (Int.ofNat p)).X q =
      ((fiberModuleCechComplexFunctor F J O).obj (I.X q)).X p :=
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

/-- Stage hypercohomology `H^q(C_p, K_p)` on the fiberwise site. -/
def fiberHypercohomologyFunctor (p : ℕ) (q : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Bounded.functor (fiberComponentSectionsFunctor F J O p) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q

/-- Evaluating fiberwise stage hypercohomology recovers the homology of the bounded-below
derived functor of `Hom(g_p! O_p, -)`. -/
theorem fiberHypercohomologyFunctor_obj (p : ℕ) (q : ℤ)
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    (fiberHypercohomologyFunctor F J O p q).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q).obj
        ((Functor.RightDerived.Bounded.functor
          (fiberComponentSectionsFunctor F J O p)).obj K) :=
  sorry

/-- Fiberwise stage hypercohomology acts on morphisms by the homology of the bounded-below
derived functor of `Hom(g_p! O_p, -)`. -/
theorem fiberHypercohomologyFunctor_map (p : ℕ) (q : ℤ)
    {K L : DerivedCategory.Plus (SheafOfModules.{w} O)} (φ : K ⟶ L) :
    (fiberHypercohomologyFunctor F J O p q).map φ =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q).map
        ((Functor.RightDerived.Bounded.functor
          (fiberComponentSectionsFunctor F J O p)).map φ) :=
  sorry

/-- Total hypercohomology `H^n(C_total, K)` on the fiberwise site. -/
def fiberTotalHypercohomologyFunctor (n : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Bounded.functor (fiberTotalSectionsFunctor F J O) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n

/-- Evaluating fiberwise total hypercohomology recovers the homology of the bounded-below
derived functor of `Hom(O, -)`. -/
theorem fiberTotalHypercohomologyFunctor_obj (n : ℤ)
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    (fiberTotalHypercohomologyFunctor F J O n).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((Functor.RightDerived.Bounded.functor
          (fiberTotalSectionsFunctor F J O)).obj K) :=
  sorry

/-- Fiberwise total hypercohomology acts on morphisms by the homology of the bounded-below
derived functor of `Hom(O, -)`. -/
theorem fiberTotalHypercohomologyFunctor_map (n : ℤ)
    {K L : DerivedCategory.Plus (SheafOfModules.{w} O)} (φ : K ⟶ L) :
    (fiberTotalHypercohomologyFunctor F J O n).map φ =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n).map
        ((Functor.RightDerived.Bounded.functor
          (fiberTotalSectionsFunctor F J O)).map φ) :=
  sorry

/-- The Čech differential on nonnegative first-page functors on the fiberwise site. -/
def fiberHypercohomology_d1 (p : ℕ) (q : ℤ) :
    fiberHypercohomologyFunctor F J O p q ⟶
      fiberHypercohomologyFunctor F J O (p + 1) q :=
  whiskerRight
    (Functor.RightDerived.Bounded.map (fiberComponentSections_d1 F J O p))
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q)

/-- First-page target `K ↦ H^q(C_p, K_p)` on the fiberwise site, vanishing for `p < 0`. -/
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

/-- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}` on the fiberwise site. -/
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

/-- First-page groups in negative Čech degree vanish on the fiberwise site. -/
theorem fiberPageOneFunctor_neg
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) {p : ℤ} (hp : p < 0)
    (q : ℤ) :
    IsZero ((fiberPageOneFunctor F J O p q).obj K) :=
  sorry

/-- Every bounded-below derived module on the total simplicial site admits a convergent
spectral sequence with stage hypercohomology on the first page and the canonical
alternating-coface differential. -/
theorem exists_spectralSequence
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    ∃ (S : WithAbutment (fun n ↦ fiberTotalHypercohomologyFunctor F J O n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (fiberPageOneFunctor F J O p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (fiberPageOneDifferential F J O p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- The stage-hypercohomology spectral sequences can be chosen simultaneously for all
bounded-below derived modules, with natural first-page comparisons and maps preserving
identities and composition on spectral sequences. -/
theorem spectralSequence_functorial :
    ∃ (S : ∀ K : DerivedCategory.Plus (SheafOfModules.{w} O),
        WithAbutment (fun n ↦ fiberTotalHypercohomologyFunctor F J O n) K)
      (pageOneIso : ∀ (K : DerivedCategory.Plus (SheafOfModules.{w} O)) (p q : ℤ),
        ((S K).sequence.page 1).X (p, q) ≅ (fiberPageOneFunctor F J O p q).obj K)
      (m : ∀ {K L : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : K ⟶ L),
        WithAbutment.Map (fun n ↦ fiberTotalHypercohomologyFunctor F J O n) f (S K) (S L)),
      (∀ (K : DerivedCategory.Plus (SheafOfModules.{w} O)) (p q : ℤ),
        (pageOneIso K p q).hom ≫ (fiberPageOneDifferential F J O p q).app K =
          ((S K).sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso K (p + 1) q).hom) ∧
      (∀ {K L : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : K ⟶ L) (p q : ℤ),
        ((m f).sequenceMap.hom 1).f (p, q) ≫ (pageOneIso L p q).hom =
          (pageOneIso K p q).hom ≫ (fiberPageOneFunctor F J O p q).map f) ∧
      (∀ K : DerivedCategory.Plus (SheafOfModules.{w} O),
        (m (𝟙 K)).sequenceMap = 𝟙 (S K).sequence) ∧
      (∀ {K L M : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : K ⟶ L) (g : L ⟶ M),
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap) :=
  sorry

end CategoryTheory.Grothendieck.ModuleCohomology
