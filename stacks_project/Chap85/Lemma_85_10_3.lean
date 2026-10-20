module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.SpectralSequence
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberSpectralSequence

/-!
# Lemma 85.10.3

In Situation 85.3.3 let `O` be a sheaf of rings. For `K` in `D⁺(O)` there is a
spectral sequence `(E_r, d_r)_{r ≥ 0}` with `E₁^{p,q} = H^q(C_p, K_p)` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}` converging to `H^{p+q}(C_total, K)`. This
spectral sequence is functorial in `K`.
-/

@[expose] public section

open CategoryTheory HomologicalComplex ComplexShape DerivedCategory Opposite
open FilteredComplex.SpectralSequence.Realization

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

open ModuleCohomology

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
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
variable [∀ p : ℕ,
    (componentSectionsFunctor C J O p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]
variable [(totalSectionsFunctor C J O).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]


/- Lemma 85.10.3: existence of the module hypercohomology spectral sequence. -/
@[stacks 0D7E] #check (CategoryTheory.SimplicialSites.ModuleCohomology.exists_spectralSequence C J O :
    ∀ (K : DerivedCategory.Plus (SheafOfModules.{w} O)),
    ∃ (S : WithAbutment (fun n ↦ totalHypercohomologyFunctor C J O n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅ (modulePageOneFunctor C J O p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (modulePageOneDifferential C J O p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom)

/- Lemma 85.10.3: simultaneous functoriality of the module hypercohomology spectral sequence. -/
@[stacks 0D7E] #check (CategoryTheory.SimplicialSites.ModuleCohomology.spectralSequence_functorial C J O :
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
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

open ModuleCohomology

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
variable [∀ p : ℕ,
    (fiberComponentSectionsFunctor F J O p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]
variable [(fiberTotalSectionsFunctor F J O).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]


/- Lemma 85.10.3: existence of the module hypercohomology spectral sequence. -/
@[stacks 0D7E] #check (CategoryTheory.Grothendieck.ModuleCohomology.exists_spectralSequence F J O :
    ∀ (K : DerivedCategory.Plus (SheafOfModules.{w} O)),
    ∃ (S : WithAbutment (fun n ↦ fiberTotalHypercohomologyFunctor F J O n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (fiberPageOneFunctor F J O p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (fiberPageOneDifferential F J O p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom)

/- Lemma 85.10.3: simultaneous functoriality of the module hypercohomology spectral sequence. -/
@[stacks 0D7E] #check (CategoryTheory.Grothendieck.ModuleCohomology.spectralSequence_functorial F J O :
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
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap))

end CategoryTheory.Grothendieck
