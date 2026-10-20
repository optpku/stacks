module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.AdicLisse
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived
open RingedSite.Hom
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ]
variable [HasSheafify (topology X) (ModuleCat.{w} Λ)]
variable [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [MonoidalCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]

-- Local declaration justification (instance diamond): `Sheaf` inherits
-- `HasZeroMorphisms` and `Preadditive` through `FullSubcategory`, whereas derived
-- tensor and exact derived functors use `Abelian.toPreadditive`. Suppress the
-- embedding instances only during parameter or declaration elaboration, and
-- restore both registrations immediately afterward.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
attribute [-instance] Preadditive.fullSubcategory

variable [MonoidalPreadditive (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [∀ (K L : CochainComplex (Sheaf (topology X) (ModuleCat.{w} Λ)) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (topology X) (ModuleCat.{w} Λ))) (ComplexShape.up ℤ)]
variable [@DerivedCategory.DerivedTensor.Right.Has (Sheaf (topology X) (ModuleCat.{w} Λ)) _ _ _ _ _ _]
variable [@DerivedCategory.DerivedTensor.Left.Has (Sheaf (topology X) (ModuleCat.{w} Λ)) _ _ _ _ _ _]
variable [(constantSheaf (topology X) (ModuleCat.{w} Λ)).Additive]
variable [PreservesFiniteLimits (constantSheaf (topology X) (ModuleCat.{w} Λ))]
variable [PreservesFiniteColimits (constantSheaf (topology X) (ModuleCat.{w} Λ))]
variable [HasWeakSheafify (topology X) CommRingCat.{w}]
variable [HasWeakSheafify (topology X) RingCat.{w}]
variable [HasWeakSheafify (topology X) AddCommGrpCat.{w}]
variable [(topology X).WEqualsLocallyBijective RingCat.{w}]
variable [(topology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [(topology X).PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{u + 1, w}]
variable [LocallySmall
  (SheafOfModules (ringSheafOfComm (ProetaleDerived.constantCoefficientRing X Λ)))]
variable [WellPowered
  (SheafOfModules (ringSheafOfComm (ProetaleDerived.constantCoefficientRing X Λ)))]

-- Tor tests on slices use the actual constant-coefficient structure-ring tensor.
variable [∀ U : X.ProEt,
  ((ProEt.topology X).over U).HasSheafCompose
    (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) AddCommGrpCat.{w}]
variable [∀ U : X.ProEt,
  ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.ProEt, @DerivedTensor.Right.Has
  (SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, w, w}
    ((ProEt.topology X).over U)
    ((constantCoefficientRing X Λ).over U)) _ _
  (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory
    ((ProEt.topology X).over U) ((constantCoefficientRing X Λ).over U)) _ _
  (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
    ((constantCoefficientRing X Λ).over U))]
variable [∀ U : RingedSite.ofCommRingSheaf (topology X)
      (ProetaleDerived.constantCoefficientRing X Λ),
  PreservesFiniteLimits
    (localizedRestriction.{w}
      (RingedSite.ofCommRingSheaf (topology X)
        (ProetaleDerived.constantCoefficientRing X Λ)) U)]
variable [∀ U : RingedSite.ofCommRingSheaf (topology X)
      (ProetaleDerived.constantCoefficientRing X Λ),
  PreservesFiniteColimits
    (localizedRestriction.{w}
      (RingedSite.ofCommRingSheaf (topology X)
        (ProetaleDerived.constantCoefficientRing X Λ)) U)]
variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
  (baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((topology Y).over U) (ModuleCat.{w} Λ)]
variable [∀ U : X.ProEt, Abelian (Sheaf ((topology X).over U) (ModuleCat.{w} Λ))]
variable [∀ U : X.ProEt, HasDerivedCategory (Sheaf ((topology X).over U) (ModuleCat.{w} Λ))]
variable [∀ U : X.ProEt, ((topology X).overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ U : X.ProEt, PreservesFiniteLimits ((topology X).overPullback (ModuleCat.{w} Λ) U)]
variable [∀ U : X.ProEt, PreservesFiniteColimits ((topology X).overPullback (ModuleCat.{w} Λ) U)]
variable [HasTerminal X.ProEt]

variable (I : Ideal Λ)
variable [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))))]
variable [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X).Additive]
variable [(Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (ComplexShape.up ℤ))]
variable [MonoidalCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))))]
variable [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))))]
variable [∀ (K L : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))))) (ComplexShape.up ℤ)]
variable [h_quotientTensor :
  @DerivedTensor.Right.Has
    (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))) _ _ _ _ _ _]
variable [LocallySmall
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))))]
variable [WellPowered
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))))]

variable [∀ U : X.ProEt, @DerivedTensor.Right.Has
  (SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, w, w}
    ((ProEt.topology X).over U)
    ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
  (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory
    ((ProEt.topology X).over U) ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
  (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
    ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U))]

variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  PreservesFiniteLimits
    (localizedRestriction.{w}
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))) U)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  PreservesFiniteColimits
    (localizedRestriction.{w}
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))) U)]
variable [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))),
  (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]

attribute [instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/- Lemma 61.29.6: let `X` be a connected scheme, `Λ` a Noetherian ring, and `I` an
ideal of `Λ`. If `K` is an object of `D_cons(X, Λ)` such that
`K ⊗ᴸ underline(Λ / I)` has locally constant cohomology sheaves, then `K` is
adic lisse in the sense of Definition 61.29.4.

Membership in `D_cons(X, Λ)` is `ProetaleDerived.IsConstructible`. The reduction
`K ⊗ᴸ underline(Λ / I)` is `proEtReduction I 1 K` in `D(X_proétale, Λ / I)`.
Locally constant cohomology is `cohomologyIn` of `Sheaf.locallyConstant` on that
reduction. The conclusion is `Derived.IsAdicLisse I K`. -/
@[stacks 09C6] #check
  (AlgebraicGeometry.Scheme.ProEt.isAdicLisse_of_locallyConstantCohomology I :
    ∀ [ConnectedSpace X] [IsNoetherianRing Λ]
      (K : ProetaleDerived X Λ) [ProetaleDerived.IsConstructible I K],
      DerivedCategory.cohomologyIn
        (Sheaf.locallyConstant (topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))))
        (proEtReduction I 1 K) → Derived.IsAdicLisse I K)

end AlgebraicGeometry.Scheme.ProEt

end
