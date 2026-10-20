/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.IdealPower
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.Sites.WeaklyContractible

/-!
# Mittag-Leffler cohomology of constant derived reductions

On a weakly contractible affine scheme, the degree-zero sections of the
canonical ideal-power reductions of a constructible complex form a
Mittag-Leffler system when every positive quotient-coefficient reduction
is a complex of constant sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProetaleDerived
open Opposite

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

-- Local declaration justification (instance diamond): module sheaves inherit
-- `HasZeroMorphisms` and `Preadditive` through `FullSubcategory`, whereas exact
-- derived functors and derived tensor use `Abelian.toPreadditive`. Each
-- suppression is confined to parameter elaboration or a single declaration.
-- The embedding instances are restored immediately after each parameter block.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory
variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
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

variable [((topology X).W : MorphismProperty (X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ)).IsMonoidal]
variable [MonoidalPreadditive (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [∀ (K L : CochainComplex (Sheaf (topology X) (ModuleCat.{w} Λ)) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (topology X) (ModuleCat.{w} Λ))) (ComplexShape.up ℤ)]
variable [DerivedTensor.Left.Has (C := Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [∀ n : ℕ, (constantSheaf (topology X) (ModuleCat.{w} (Λ ⧸ I ^ (n + 1)))).Additive]
variable [∀ n : ℕ, PreservesFiniteLimits
  (constantSheaf (topology X) (ModuleCat.{w} (Λ ⧸ I ^ (n + 1))))]
variable [∀ n : ℕ, PreservesFiniteColimits
  (constantSheaf (topology X) (ModuleCat.{w} (Λ ⧸ I ^ (n + 1))))]

attribute [instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- On a weakly contractible affine scheme over a Noetherian coefficient ring,
the degree-zero sections of the canonical ideal-power derived reductions of a
constructible complex form a Mittag-Leffler system if every positive reduction
is a complex of constant sheaves over its quotient coefficient ring. The tensor
on module sheaves is induced by the canonical monoidal sheafification. -/
theorem degreeZeroSectionsSystem_isMittagLeffler
    [IsAffine X]
    [(topology X).IsWeaklyContractible (ProEt.mk (𝟙 X))]
    (K : ProetaleDerived X Λ)
    [ProetaleDerived.IsConstructible I K]
    (hconst : ∀ n : ℕ, IsConstantComplex (proEtReduction I (n + 1) K)) :
    SequentialInverseSystem.IsMittagLeffler (degreeZeroSectionsSystem I K) := sorry

end AlgebraicGeometry.Scheme.ProEt

end
