module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Sets.OpenCover
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedRestriction
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.CompletedConstantModel

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived
open AlgebraicGeometry.Scheme.ProEt.Derived
open RingedSite.Hom
open TopologicalSpace Function
open Opposite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ]
variable [HasSheafify (topology X) (ModuleCat.{w} Λ)]
variable [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- derived tensor and `mapDerivedCategory` are typed using `Abelian.toPreadditive`.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
attribute [-instance] Preadditive.fullSubcategory

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

variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
  (baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((topology Y).over U) (ModuleCat.{w} Λ)]

variable (I : Ideal Λ)
variable [HasSheafify (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ)))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))))]
variable [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X).Additive]
variable [(Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) (ComplexShape.up ℤ))]
variable [LocallySmall
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))))]
variable [WellPowered
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))))]

variable [∀ U : X.ProEt,
  ((ProEt.topology X).over U).HasSheafCompose
    (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) AddCommGrpCat.{w}]
variable [∀ U : X.ProEt,
  ((ProEt.topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

-- Slice Tor tests use the canonical tensor and derived structure on modules over
-- the constant quotient-coefficient ring sheaf.
variable [∀ U : X.ProEt, @DerivedTensor.Right.Has
    (SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, w, w}
      ((ProEt.topology X).over U) ((constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ))).over U)) _ _
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

/-- On a weakly contractible affine scheme over a Noetherian coefficient ring, a
constructible derived object whose reduction modulo the ideal has locally constant
cohomology admits a finite disjoint open cover on which it is represented by a
bounded complex of completed constant sheaves of finite projective modules over
the adic completion. Its differentials are arbitrary morphisms of sheaves. -/
theorem exists_finiteDisjointOpenCover_termwiseCompletedConstantModel
    [IsAffine X] [IsNoetherianRing Λ]
    [(topology X).IsWeaklyContractible (ProEt.mk (𝟙 X))]
    (K : ProetaleDerived X Λ)
    [ProetaleDerived.IsConstructible I K]
    (h_loc : DerivedCategory.cohomologyIn
      (fun F : Sheaf (topology X) (ModuleCat.{w} (Λ ⧸ I ^ (1 : ℕ))) ↦
        Sheaf.IsLocallyConstant F)
      (proEtReduction I 1 K))
    [∀ U : X.Opens, Abelian (Sheaf (topology (U.toScheme)) (ModuleCat.{w} Λ))]
    [∀ U : X.Opens, HasDerivedCategory (Sheaf (topology (U.toScheme)) (ModuleCat.{w} Λ))] :
    ∃ (n : ℕ) (U : Fin n → X.Opens),
      Pairwise (Disjoint on fun i ↦ (U i : Set X)) ∧
        IsOpenCover U ∧
          ∀ i, HasTermwiseCompletedConstantModel (topology ((U i).toScheme)) I
            ((restrictDerived ((U i).ι)).obj K) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt

end
