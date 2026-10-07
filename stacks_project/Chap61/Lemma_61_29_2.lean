module

public import Mathlib.Data.PNat.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import stacks_project.Chap61.Definition_61_29_1_Constructible
public import stacks_project.Chap61.Definition_61_29_1_Derived
public import stacks_project.Chap61.Lemma_61_19_11_Reduction
public import stacks_project.Chap61.Lemma_61_19_1_Comparison
public import stacks_project.Chap61.Lemma_61_27_2_Comparison
public import stacks_project.Chap61.Lemma_61_29_5_Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.29.2

On a quasi-compact scheme, an object of `D_cons(X, Λ)` is a homotopy limit of
its ideal-power reductions, with a uniform vanishing/Tor-amplitude interval,
constructible cohomology, and étale `D_ctf` preimages under `ε⁻¹`.
-/

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
open ComplexShape
open RingedSite.Hom
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProetaleDerived

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [MonoidalCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]

-- Local declaration justification (instance diamond): Sheaf FullSubcategory HasZeroMorphisms vs Abelian.toPreadditive used by derived tensor.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
-- Local declaration justification (instance diamond): Sheaf FullSubcategory Preadditive vs Abelian.toPreadditive used by mapDerivedCategory.
attribute [-instance] Preadditive.fullSubcategory
-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible and not global; needed to elaborate `DerivedTensor.Right.Has` and 08FZ local Tor on constant-coefficient localizations.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [∀ (K L : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) (up ℤ)]
variable [h_derivedTensorRight :
  @DerivedTensor.Right.Has (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    _ _ _ _ _ _]
variable [h_derivedTensorLeft :
  @DerivedTensor.Left.Has (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    _ _ _ _ _ _]
variable [HasWeakSheafify (ProEt.topology X) CommRingCat.{u + 1}]
variable [HasWeakSheafify (ProEt.topology X) RingCat.{u + 1}]
variable [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}]
variable [(ProEt.topology X).WEqualsLocallyBijective RingCat.{u + 1}]
variable [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [(ProEt.topology X).HasSheafCompose (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})]
variable [(ProEt.topology X).PreservesSheafification
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [UnivLE.{u + 1, u + 1}]
variable [LocallySmall
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [WellPowered
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]

variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  MonoidalCategory
    (RingedSite.ModuleCat.{u + 1}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X Λ)).localization U))]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  MonoidalPreadditive
    (RingedSite.ModuleCat.{u + 1}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X Λ)).localization U))]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  ∀ (K L : CochainComplex
      (RingedSite.ModuleCat.{u + 1}
        ((RingedSite.ofCommRingSheaf (ProEt.topology X)
          (constantCoefficientRing X Λ)).localization U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (RingedSite.ModuleCat.{u + 1}
          ((RingedSite.ofCommRingSheaf (ProEt.topology X)
            (constantCoefficientRing X Λ)).localization U)))
      (up ℤ)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  @DerivedTensor.Right.Has
    (RingedSite.ModuleCat.{u + 1}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X Λ)).localization U))
    _ _ _ _ _ _]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  PreservesFiniteLimits
    (localizedRestriction.{u + 1}
      (RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X Λ)) U)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  PreservesFiniteColimits
    (localizedRestriction.{u + 1}
      (RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X Λ)) U)]
variable [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) (ModuleCat.{u + 1} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
  (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{u + 1} Λ)]

/-- Vanishing of cohomology outside `[a, b]` is the conjunction of the canonical
t-structure bounds `IsGE a` and `IsLE b`. -/
theorem isGE_isLE_iff_homology_isZero (K : ProetaleDerived X Λ) (a b : ℤ) :
    K.IsGE a ∧ K.IsLE b ↔
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (ProetaleModuleSheaf X Λ) i).obj K) :=
  sorry

/-- The same-category reduction `idealPowerTensor I K 1` is isomorphic to
`reduction I K`. -/
theorem idealPowerTensor_one_iso_reduction (I : Ideal Λ) (K : ProetaleDerived X Λ) :
    Nonempty (idealPowerTensor I K 1 ≅ reduction I K) :=
  sorry

variable (I : Ideal Λ)
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ)))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ))))]
variable [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X).Additive]
variable [(Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
variable [MonoidalCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ))))]
variable [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ))))]
variable [∀ (K L : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ)))) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ))))) (ComplexShape.up ℤ)]
variable [h_quotientTensor :
  @DerivedTensor.Right.Has
    (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ)))) _ _ _ _ _ _]
variable [LocallySmall
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))))]
variable [WellPowered
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))))]

variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  MonoidalCategory
    (RingedSite.ModuleCat.{u + 1}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U))]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  MonoidalPreadditive
    (RingedSite.ModuleCat.{u + 1}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U))]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  ∀ (K L : CochainComplex
      (RingedSite.ModuleCat.{u + 1}
        ((RingedSite.ofCommRingSheaf (ProEt.topology X)
          (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (RingedSite.ModuleCat.{u + 1}
          ((RingedSite.ofCommRingSheaf (ProEt.topology X)
            (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U)))
      (ComplexShape.up ℤ)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  @DerivedTensor.Right.Has (RingedSite.ModuleCat.{u + 1}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U)) _ _ _ _ _ _]

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
variable [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) (ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ)))]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ))),
  (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ)))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{u + 1} (Λ ⧸ I ^ (1 : ℕ)))]


/-- Lemma 61.29.2 (1): if `K` is in `D_cons(X, Λ)` and `X` is quasi-compact, then
`K` is a homotopy limit of `n ↦ K ⊗ᴸ underline(Λ / I ^ n)`, and there exist
`a, b` such that `H^i(K) = 0` for `i ∉ [a, b]`. -/
@[stacks 09C2]
theorem isHomotopyLimit_and_exists_isGE_isLE [CompactSpace X] 
    (K : ProetaleDerived X Λ) [IsConstructible I K] :
    HomotopyLimit.IsOf (idealPowerTensorSystem I K) K ∧
      ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b :=
  sorry

/-- `K` is a homotopy limit of the inverse system `n ↦ K ⊗ᴸ underline(Λ / I ^ n)`. -/
theorem isHomotopyLimit_idealPowerTensorSystem [CompactSpace X] 
    (K : ProetaleDerived X Λ) [IsConstructible I K] :
    HomotopyLimit.IsOf (idealPowerTensorSystem I K) K :=
  sorry

/-- There is a cohomological interval containing the cohomology of `K`. -/
theorem exists_isGE_isLE [CompactSpace X] 
    (K : ProetaleDerived X Λ) [IsConstructible I K] :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b :=
  sorry

/-- Lemma 61.29.2 (2): there is a uniform interval `[a, b]` in which every
positive-power reduction `proEtReduction I n K` in `D(X_proétale, Λ ⧸ I ^ n)` has
Tor amplitude. -/
@[stacks 09C2]
theorem exists_hasTorAmplitudeIn_proEtReduction [CompactSpace X] 
    (K : ProetaleDerived X Λ) [IsConstructible I K]
    [∀ n : ℕ+, HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ n : ℕ+, HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ n : ℕ+, (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [∀ n : ℕ+,
      (Functor.Homotopy.toDerived
          (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    [∀ n : ℕ+, ∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ n : ℕ+, ∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ n : ℕ+, ∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [∀ n : ℕ+, MonoidalCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ n : ℕ+, MonoidalPreadditive
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ n : ℕ+, ∀ (A B : CochainComplex
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))) ℤ),
      HomologicalComplex.HasMapBifunctor A B
        (curriedTensor
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))))
        (ComplexShape.up ℤ)]
    [∀ n : ℕ+,
      @DerivedTensor.Right.Has
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))
        _ _ _ _ _ _] :
    ∃ a b : ℤ, ∀ n : ℕ+,
      DerivedTensor.HasTorAmplitudeIn (proEtReduction I n K) a b :=
  sorry

/-- A uniform Tor-amplitude interval for the reductions `proEtReduction I n K`
is a vanishing interval for `K`. -/
theorem isGE_isLE_of_hasTorAmplitudeIn [CompactSpace X] 
    (K : ProetaleDerived X Λ) [IsConstructible I K]
    [∀ n : ℕ+, HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ n : ℕ+, HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ n : ℕ+, (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [∀ n : ℕ+,
      (Functor.Homotopy.toDerived
          (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    [∀ n : ℕ+, ∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ n : ℕ+, ∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ n : ℕ+, ∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [∀ n : ℕ+, MonoidalCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ n : ℕ+, MonoidalPreadditive
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ n : ℕ+, ∀ (A B : CochainComplex
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))) ℤ),
      HomologicalComplex.HasMapBifunctor A B
        (curriedTensor
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))))
        (ComplexShape.up ℤ)]
    [∀ n : ℕ+,
      @DerivedTensor.Right.Has
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))
        _ _ _ _ _ _]
    {a b : ℤ}
    (h : ∀ n : ℕ+, DerivedTensor.HasTorAmplitudeIn (proEtReduction I n K) a b) :
    K.IsGE a ∧ K.IsLE b :=
  sorry

/-- There exist `a, b` that are simultaneously a vanishing interval for `K` and a
Tor-amplitude interval for every positive-power reduction `proEtReduction I n K`. -/
theorem exists_isGE_isLE_hasTorAmplitudeIn_proEtReduction [CompactSpace X]
    (K : ProetaleDerived X Λ) [IsConstructible I K]
    [∀ n : ℕ+, HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ n : ℕ+, HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ n : ℕ+, (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [∀ n : ℕ+,
      (Functor.Homotopy.toDerived
          (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    [∀ n : ℕ+, ∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ n : ℕ+, ∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ n : ℕ+, ∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [∀ n : ℕ+, MonoidalCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ n : ℕ+, MonoidalPreadditive
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ n : ℕ+, ∀ (A B : CochainComplex
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))) ℤ),
      HomologicalComplex.HasMapBifunctor A B
        (curriedTensor
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))))
        (ComplexShape.up ℤ)]
    [∀ n : ℕ+,
      @DerivedTensor.Right.Has
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))
        _ _ _ _ _ _] :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b ∧ ∀ n : ℕ+,
      DerivedTensor.HasTorAmplitudeIn (proEtReduction I n K) a b :=
  sorry

/-- Lemma 61.29.2 (3): each positive-power reduction `proEtReduction I n K` has
constructible cohomology sheaves as a complex of `Λ / I ^ n`-modules. -/
@[stacks 09C2]
theorem proEtReduction_cohomologyIn_constructible [CompactSpace X] 
    (K : ProetaleDerived X Λ) [IsConstructible I K] (n : ℕ+)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    [∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P] :
    cohomologyIn (constructibleProEtaleModule X (Λ ⧸ I ^ (n : ℕ)))
      (proEtReduction I n K) :=
  sorry

/-- Restriction of scalars of `proEtReduction I n K` is isomorphic to the
same-category derived tensor `idealPowerTensor I K n`. -/
theorem restrictScalars_proEtReduction_iso_idealPowerTensor 
    (K : ProetaleDerived X Λ) (n : ℕ)
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
      (proEtModuleRestrictScalars (Ideal.Quotient.mk (I ^ n)) X)] :
    Nonempty
      ((proEtDerivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X).obj
          (proEtReduction I n K) ≅
        idealPowerTensor I K n) :=
  sorry

/-- Lemma 61.29.2 (4): each positive-power reduction `proEtReduction I n K` is
`ε⁻¹ L` for some `L` in `D_ctf(X_étale, Λ / I ^ n)`. -/
@[stacks 09C2]
theorem exists_etaleConstructibleTorFinite [CompactSpace X] 
    (K : ProetaleDerived X Λ) [IsConstructible I K] (n : ℕ+)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [HasDerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)),
      (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n : ℕ))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    [(etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).Additive]
    [PreservesFiniteLimits
      (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [PreservesFiniteColimits
      (etaleToProEtPullback X (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ Y : Scheme.{u},
      HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ Y : Scheme.{u},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [MonoidalCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [MonoidalPreadditive
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))]
    [∀ (A B : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))) ℤ),
      HomologicalComplex.HasMapBifunctor A B
        (curriedTensor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))))
        (ComplexShape.up ℤ)]
    [h_derivedTensor_etale :
      @DerivedTensor.Right.Has
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))
        _ _ _ _ _ _] :
    ∃ (L : DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ))))),
      cohomologyIn (constructibleEtaleModule X (Λ ⧸ I ^ (n : ℕ))) L ∧
        DerivedTensor.HasFiniteTorDimension L ∧
          Nonempty
            ((etaleToProEtPullback X
                (ModuleCat.{u + 1} (Λ ⧸ I ^ (n : ℕ)))).mapDerivedCategory.obj L ≅
              proEtReduction I n K) :=
  sorry

end AlgebraicGeometry.Scheme.ProetaleDerived

end

end
