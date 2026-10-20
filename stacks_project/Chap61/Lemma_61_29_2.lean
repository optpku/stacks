module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.Reduction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProetaleDerived

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [((ProEt.topology X).W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]

section CanonicalTensor

-- Local declaration justification (instance diamond): module sheaves inherit
-- zero morphisms and addition from FullSubcategory, whereas the derived tensor
-- and exact derived functors use Abelian.toPreadditive. Suppress the embedding
-- instances only in this section so all dependent tensor hypotheses agree.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
  Preadditive.fullSubcategory

variable [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [∀ (A B : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ),
  HomologicalComplex.HasMapBifunctor A B
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) (ComplexShape.up ℤ)]
variable [DerivedTensor.Right.Has (C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [DerivedTensor.Left.Has (C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]

#check (AlgebraicGeometry.Scheme.ProetaleDerived.idealPowerTensor_one_iso_reduction :
  ∀ (I : Ideal Λ) (K : ProetaleDerived X Λ),
    Nonempty (idealPowerTensor I K 1 ≅ reduction I K))

#check (AlgebraicGeometry.Scheme.ProetaleDerived.restrictScalars_proEtReduction_iso_idealPowerTensor :
  ∀ (I : Ideal Λ) (K : ProetaleDerived X Λ) (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    [(ProEt.topology X).HasSheafCompose
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n)))]
    [(proEtModuleRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [PreservesFiniteLimits
      (proEtModuleRestrictScalars (Ideal.Quotient.mk (I ^ n)) X)]
    [PreservesFiniteColimits
      (proEtModuleRestrictScalars (Ideal.Quotient.mk (I ^ n)) X)],
    Nonempty
      ((proEtDerivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
          (proEtReduction I n K) ≅
        idealPowerTensor I K n))


variable [HasWeakSheafify (ProEt.topology X) CommRingCat.{u + 1}]
variable [HasWeakSheafify (ProEt.topology X) RingCat.{u + 1}]
variable [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}]
variable [(ProEt.topology X).WEqualsLocallyBijective RingCat.{u + 1}]
variable [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [(ProEt.topology X).HasSheafCompose (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})]
variable [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [UnivLE.{u + 1, u + 1}]
variable [LocallySmall.{u + 1}
  (SheafOfModules.{u + 1} (ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [WellPowered.{u + 1}
  (SheafOfModules.{u + 1} (ringSheafOfComm (constantCoefficientRing X Λ)))]

-- Slice Tor-dimension uses the structure-ring tensor on the constant coefficient sheaf.
variable [∀ U : X.ProEt,
  ((ProEt.topology X).over U).HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) AddCommGrpCat.{u + 1}]
variable [∀ U : X.ProEt,
  ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [∀ U : X.ProEt, @DerivedTensor.Right.Has
    (SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      ((ProEt.topology X).over U) ((constantCoefficientRing X Λ).over U)) _ _
    (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory
      ((ProEt.topology X).over U) ((constantCoefficientRing X Λ).over U)) _ _
    (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
      ((constantCoefficientRing X Λ).over U))]


variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  PreservesFiniteLimits
    (localizedRestriction.{u + 1}
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)) U)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  PreservesFiniteColimits
    (localizedRestriction.{u + 1}
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)) U)]
variable [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) (ModuleCat.{u + 1} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
  (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{u + 1} Λ)]

variable [IsNoetherianRing Λ] (I : Ideal Λ)
variable [∀ n : ℕ, HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
variable [∀ n : ℕ, HasDerivedCategory
  (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
variable [∀ n : ℕ, (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
variable [∀ n : ℕ,
  (Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]

variable [LocallySmall.{u + 1}
  (SheafOfModules.{u + 1} (ringSheafOfComm (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))))]
variable [WellPowered.{u + 1}
  (SheafOfModules.{u + 1} (ringSheafOfComm (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))))]

variable [∀ U : X.ProEt, @DerivedTensor.Right.Has
    (SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      ((ProEt.topology X).over U) ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
    (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory
      ((ProEt.topology X).over U) ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
    (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
      ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U))]

variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  PreservesFiniteLimits
    (localizedRestriction.{u + 1}
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))) U)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  PreservesFiniteColimits
    (localizedRestriction.{u + 1}
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))) U)]
variable [∀ n : ℕ, ∀ Y : Scheme.{u},
  HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
variable [∀ n : ℕ, ∀ (Y : Scheme.{u}) (U : Y.ProEt),
  HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
variable [∀ n : ℕ, ∀ {Y : Scheme.{u}} (f : Y ⟶ X)
    (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
  (ProEt.baseChange f).op.HasLeftKanExtension P]

variable (K : ProetaleDerived X Λ) [hK : IsConstructible I K]

variable [∀ n : ℕ+, ((ProEt.topology X).W
  (A := ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).IsMonoidal]
variable [∀ n : ℕ+, MonoidalPreadditive
  (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
variable [∀ n : ℕ+, ∀ (A B : CochainComplex
    (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))) ℤ),
  HomologicalComplex.HasMapBifunctor A B
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))))
    (ComplexShape.up ℤ)]
variable [∀ n : ℕ+, DerivedTensor.Right.Has
  (C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
variable [∀ n : ℕ+, HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
variable [∀ n : ℕ+, ∀ Y : Scheme.{u},
  HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
variable [∀ n : ℕ+, ∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
variable [∀ n : ℕ+, ∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
    (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ n : ℕ+, HasDerivedCategory
  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
variable [∀ n : ℕ+, ∀ U : X.Etale,
  Abelian (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
variable [∀ n : ℕ+, ∀ U : X.Etale,
  HasDerivedCategory (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
variable [∀ n : ℕ+, ∀ U : X.Etale,
  ((X.smallEtaleTopology.over U).W (A := ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).IsMonoidal]
variable [∀ n : ℕ+, ∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)),
  (etaleToProEt X).op.HasLeftKanExtension F]
variable [∀ n : ℕ+,
  (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).Additive]
variable [∀ n : ℕ+, PreservesFiniteLimits
  (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
variable [∀ n : ℕ+, PreservesFiniteColimits
  (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]

variable [CompactSpace X]

/- Lemma 61.29.2: a constructible pro-étale complex is recovered from its
ideal-power reductions, with common cohomological and Tor-amplitude bounds,
constructible reduction cohomology, and constructible Tor-finite étale preimages. -/
@[stacks 09C2] #check
  (AlgebraicGeometry.Scheme.ProetaleDerived.constructible_reductions I K :
    HomotopyLimit.IsOf (idealPowerTensorSystem I K) K ∧
      ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b ∧
        (∀ n : ℕ+, DerivedTensor.HasTorAmplitudeIn (proEtReduction I n K) a b) ∧
        (∀ n : ℕ+, cohomologyIn
          (constructibleProEtaleModule X (Λ ⧸ I ^ (n : ℕ))) (proEtReduction I n K)) ∧
        (∀ n : ℕ+, ∃ L : AlgebraicGeometry.Scheme.Etale.Derived.ConstructibleTorFinite
            X (Λ ⧸ I ^ (n : ℕ)),
          Nonempty ((etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).mapDerivedCategory.obj
            L.obj ≅ proEtReduction I n K)))

end CanonicalTensor

end AlgebraicGeometry.Scheme.ProetaleDerived
