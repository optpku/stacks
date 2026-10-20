/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.MittagLeffler
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProetaleDerived
open AlgebraicGeometry.Scheme.ProEt Opposite

noncomputable section

universe u w

-- Local declaration justification (instance diamond): use `Abelian.toPreadditive`
-- for exact derived functors and tensor, rather than the sheaf full-subcategory
-- embedding, only while elaborating these parameters and the typed check.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/- Lemma 61.29.5
The canonical degree-zero cohomology system of a constructible complex with
constant positive quotient-coefficient reductions is Mittag-Leffler on a
weakly contractible affine scheme. -/
@[stacks 09C5] #check
  (AlgebraicGeometry.Scheme.ProEt.degreeZeroSectionsSystem_isMittagLeffler :
    ∀ {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [HasSheafify (ProEt.topology X) (ModuleCat.{w} Λ)]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
    [HasWeakSheafify (ProEt.topology X) CommRingCat.{w}]
    [HasWeakSheafify (ProEt.topology X) RingCat.{w}]
    [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{w}]
    [(ProEt.topology X).WEqualsLocallyBijective RingCat.{w}]
    [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [(ProEt.topology X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
    [UnivLE.{u + 1, w}]
    [LocallySmall
      (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
    [WellPowered
      (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
    [∀ U : X.ProEt,
      ((ProEt.topology X).over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) AddCommGrpCat.{w}]
    [∀ U : X.ProEt,
      ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} Λ)]
    (I : Ideal Λ)
    [∀ n : ℕ, HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (n + 1)))]
    [∀ n : ℕ, HasDerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (n + 1))))]
    [∀ n : ℕ, (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n + 1))) X).Additive]
    [∀ n : ℕ, (Functor.Homotopy.toDerived
      (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (n + 1))) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (ComplexShape.up ℤ))]
    [∀ U : X.ProEt, @DerivedTensor.Right.Has
      (SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, w, w}
        ((ProEt.topology X).over U)
        ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
      (RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory
        ((ProEt.topology X).over U)
        ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
      (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
        ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U))]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X)
      (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [∀ {Y : Scheme.{u}},
      HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]
    [∀ {Y : Scheme.{u}} (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U)
        (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]

    [((topology X).W : MorphismProperty (X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ)).IsMonoidal]
    [MonoidalPreadditive (Sheaf (topology X) (ModuleCat.{w} Λ))]
    [∀ (K L : CochainComplex (Sheaf (topology X) (ModuleCat.{w} Λ)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (Sheaf (topology X) (ModuleCat.{w} Λ))) (ComplexShape.up ℤ)]
    [DerivedTensor.Left.Has (C := Sheaf (topology X) (ModuleCat.{w} Λ))]
    [∀ n : ℕ, (constantSheaf (topology X) (ModuleCat.{w} (Λ ⧸ I ^ (n + 1)))).Additive]
    [∀ n : ℕ, PreservesFiniteLimits
      (constantSheaf (topology X) (ModuleCat.{w} (Λ ⧸ I ^ (n + 1))))]
    [∀ n : ℕ, PreservesFiniteColimits
      (constantSheaf (topology X) (ModuleCat.{w} (Λ ⧸ I ^ (n + 1))))]
      [IsAffine X]
      [(topology X).IsWeaklyContractible (ProEt.mk (𝟙 X))]
      (K : ProetaleDerived X Λ) [ProetaleDerived.IsConstructible I K],
      (∀ n : ℕ, IsConstantComplex (proEtReduction I (n + 1) K)) →
        SequentialInverseSystem.IsMittagLeffler (degreeZeroSectionsSystem I K))

end
