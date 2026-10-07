module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import stacks_project.Chap61.Definition_61_29_1_Constructible
public import stacks_project.Chap61.Lemma_61_29_5_Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.29.5

On a weakly contractible affine scheme, degree-zero cohomology of the
ideal-power derived reductions of a constructible complex with constant
reductions is Mittag-Leffler.
-/

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
open Opposite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ]
variable [HasSheafify (topology X) (ModuleCat.{w} Λ)]
variable [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [MonoidalCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- derived tensor and `mapDerivedCategory` are typed using `Abelian.toPreadditive`.
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

variable [∀ U : RingedSite.ofCommRingSheaf (topology X)
      (ProetaleDerived.constantCoefficientRing X Λ),
  MonoidalCategory
    (RingedSite.ModuleCat.{w}
      ((RingedSite.ofCommRingSheaf (topology X)
        (ProetaleDerived.constantCoefficientRing X Λ)).localization U))]
variable [∀ U : RingedSite.ofCommRingSheaf (topology X)
      (ProetaleDerived.constantCoefficientRing X Λ),
  MonoidalPreadditive
    (RingedSite.ModuleCat.{w}
      ((RingedSite.ofCommRingSheaf (topology X)
        (ProetaleDerived.constantCoefficientRing X Λ)).localization U))]
variable [∀ U : RingedSite.ofCommRingSheaf (topology X)
      (ProetaleDerived.constantCoefficientRing X Λ),
  ∀ (K L : CochainComplex
      (RingedSite.ModuleCat.{w}
        ((RingedSite.ofCommRingSheaf (topology X)
          (ProetaleDerived.constantCoefficientRing X Λ)).localization U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (RingedSite.ModuleCat.{w}
          ((RingedSite.ofCommRingSheaf (topology X)
            (ProetaleDerived.constantCoefficientRing X Λ)).localization U)))
      (ComplexShape.up ℤ)]
variable [∀ U : RingedSite.ofCommRingSheaf (topology X)
      (ProetaleDerived.constantCoefficientRing X Λ),
  @DerivedTensor.Right.Has (RingedSite.ModuleCat.{w}
      ((RingedSite.ofCommRingSheaf (topology X)
        (ProetaleDerived.constantCoefficientRing X Λ)).localization U)) _ _ _ _ _ _]
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

variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  MonoidalCategory
    (RingedSite.ModuleCat.{w}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U))]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  MonoidalPreadditive
    (RingedSite.ModuleCat.{w}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U))]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  ∀ (K L : CochainComplex
      (RingedSite.ModuleCat.{w}
        ((RingedSite.ofCommRingSheaf (ProEt.topology X)
          (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (RingedSite.ModuleCat.{w}
          ((RingedSite.ofCommRingSheaf (ProEt.topology X)
            (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U)))
      (ComplexShape.up ℤ)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  @DerivedTensor.Right.Has (RingedSite.ModuleCat.{w}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U)) _ _ _ _ _ _]

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


/-- Lemma 61.29.5: let `X` be a weakly contractible affine scheme, `Λ` a Noetherian ring,
and `I` an ideal of `Λ`. If `K` is an object of `D_cons(X, Λ)` such that each derived
reduction `idealPowerTensor I K n` is isomorphic in `D(X_proétale, Λ / I ^ n)` to a
complex of constant sheaves of `Λ / I ^ n`-modules, then the inverse system
`degreeZeroSectionsSystem I K` of modules `n ↦ H^0(X, K ⊗ᴸ Λ / I ^ n)` satisfies the
Mittag-Leffler condition.

Membership in `D_cons(X, Λ)` is `ProetaleDerived.IsConstructible`: derived completeness
with respect to `I`, constructible cohomology and local finite Tor dimension of `proEtReduction I 1 K`
over the quotient coefficient ring. Constant complexes in
`D(X_proétale, Λ / I ^ n)` are encoded by `IsConstantComplex` after restriction of
scalars, matching Lemma 61.28.3. -/
@[stacks 09C5]
theorem degreeZeroSectionsSystem_isMittagLeffler
    [IsAffine X] [IsNoetherianRing Λ]
    [(topology X).IsWeaklyContractible (ProEt.mk (𝟙 X))]
    (K : ProetaleDerived X Λ)
    [ProetaleDerived.IsConstructible I K]
    (hconst : ∀ n, IsConstantComplex (idealPowerTensor I K n)) :
    SequentialInverseSystem.IsMittagLeffler (degreeZeroSectionsSystem I K) := sorry

end AlgebraicGeometry.Scheme.ProEt

end
