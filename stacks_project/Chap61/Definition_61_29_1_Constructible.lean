module

public import stacks_project.Chap61.Definition_61_29_1_Derived
public import stacks_project.Chap61.Lemma_61_19_11_Reduction
public import stacks_project.Chap61.Definition_61_28_1_Constructible
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Local
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open RingedSite.Hom
open scoped ZeroObject

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.ProetaleDerived

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{v} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
variable [MonoidalCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]

-- Local declaration justification (instance diamond): `Sheaf` is a `FullSubcategory`,
-- so `HasZeroMorphisms`/`Preadditive` are synthesized from that embedding, while
-- derived tensor and `mapDerivedCategory` are typed using `Abelian.toPreadditive`.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
attribute [-instance] Preadditive.fullSubcategory
-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is a reducible
-- standard derived-category owner, not a global instance; localizations of the constant
-- coefficient site need it to elaborate `DerivedTensor.Right.Has` and 08FZ local Tor
-- dimension, matching the ReasLib ringed-site derived-category presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))]
variable [∀ (K L : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
variable [h_derivedTensor :
  @DerivedTensor.Right.Has
    (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) _ _ _ _ _ _]
variable [HasWeakSheafify (ProEt.topology X) CommRingCat.{v}]
variable [HasWeakSheafify (ProEt.topology X) RingCat.{v}]
variable [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{v}]
variable [(ProEt.topology X).WEqualsLocallyBijective RingCat.{v}]
variable [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(ProEt.topology X).HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
variable [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
variable [UnivLE.{u + 1, v}]
variable [LocallySmall
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [WellPowered
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]

/-- Localized module categories over the constant ring sheaf of `Λ` carry the standard
derived-category structure. -/
@[reducible] noncomputable instance hasDerivedCategory_constantCoefficient_localization
    (U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X Λ)).carrier) :
    HasDerivedCategory
      (RingedSite.ModuleCat.{v}
        ((RingedSite.ofCommRingSheaf (ProEt.topology X)
          (constantCoefficientRing X Λ)).localization U)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory
    ((RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).localization U)

variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  MonoidalCategory
    (RingedSite.ModuleCat.{v}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X Λ)).localization U))]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  MonoidalPreadditive
    (RingedSite.ModuleCat.{v}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X Λ)).localization U))]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  ∀ (K L : CochainComplex
      (RingedSite.ModuleCat.{v}
        ((RingedSite.ofCommRingSheaf (ProEt.topology X)
          (constantCoefficientRing X Λ)).localization U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (RingedSite.ModuleCat.{v}
          ((RingedSite.ofCommRingSheaf (ProEt.topology X)
            (constantCoefficientRing X Λ)).localization U)))
      (ComplexShape.up ℤ)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  @DerivedTensor.Right.Has (RingedSite.ModuleCat.{v}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X Λ)).localization U)) _ _ _ _ _ _]

/-- Localized module categories over the constant ring sheaf of `Λ` support unbounded
fixed-right derived tensoring. -/
instance instDerivedTensorRightHas_constantCoefficient_localization
    (U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X Λ)).carrier) :
    @DerivedTensor.Right.Has (RingedSite.ModuleCat.{v}
        ((RingedSite.ofCommRingSheaf (ProEt.topology X)
          (constantCoefficientRing X Λ)).localization U)) _ _ _ _ _ _ :=
  sorry

variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  PreservesFiniteLimits
    (localizedRestriction.{v}
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)) U)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X Λ)).carrier,
  PreservesFiniteColimits
    (localizedRestriction.{v}
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)) U)]
variable [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) (ModuleCat.{v} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{v} Λ),
  (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{v} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{v} Λ)]

/-- Sheaf-level constructible `Λ`-modules on `X_proétale`, as an object property. -/
abbrev constructibleModule :
    ObjectProperty (ProetaleModuleSheaf X Λ) :=
  fun F ↦ ProEt.IsConstructibleModule F

/-- Membership in `constructibleModule` is sheaf-level constructibility. -/
theorem constructibleModule_apply (F : ProetaleModuleSheaf X Λ) :
    constructibleModule F ↔ ProEt.IsConstructibleModule F := sorry

/-- The 08FZ covering-local finite Tor-dimension condition after transport of an object of
`D(X_proétale, Λ)` to the constant-`Λ` ringed site. -/
def locallyHasFiniteTorDimension (K : ProetaleDerived X Λ) : Prop :=
  ModuleDerived.LocallyHasFiniteTorDimension (toConstantModuleDerived K)

/-- Local finite Tor dimension on `D(X_proétale, Λ)` is the ringed-site 08FZ predicate on the
constant-coefficient image. -/
theorem locallyHasFiniteTorDimension_iff (K : ProetaleDerived X Λ) :
    locallyHasFiniteTorDimension K ↔
      ModuleDerived.LocallyHasFiniteTorDimension (toConstantModuleDerived K) := sorry

variable (I : Ideal Λ)
variable [HasSheafify (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ))))]
variable [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X).Additive]
variable [(Functor.Homotopy.toDerived
    (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ (1 : ℕ))) X)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X) (ModuleCat.{v} Λ)) (ComplexShape.up ℤ))]
variable [MonoidalCategory (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ))))]
variable [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ))))]
variable [∀ (K L : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ))))) (ComplexShape.up ℤ)]
variable [h_quotientTensor :
  @DerivedTensor.Right.Has
    (Sheaf (ProEt.topology X) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))) _ _ _ _ _ _]
variable [LocallySmall
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))))]
variable [WellPowered
  (SheafOfModules (ringSheafOfComm (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))))]

variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  MonoidalCategory
    (RingedSite.ModuleCat.{v}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U))]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  MonoidalPreadditive
    (RingedSite.ModuleCat.{v}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U))]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  ∀ (K L : CochainComplex
      (RingedSite.ModuleCat.{v}
        ((RingedSite.ofCommRingSheaf (ProEt.topology X)
          (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (RingedSite.ModuleCat.{v}
          ((RingedSite.ofCommRingSheaf (ProEt.topology X)
            (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U)))
      (ComplexShape.up ℤ)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  @DerivedTensor.Right.Has (RingedSite.ModuleCat.{v}
      ((RingedSite.ofCommRingSheaf (ProEt.topology X)
        (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).localization U)) _ _ _ _ _ _]

variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  PreservesFiniteLimits
    (localizedRestriction.{v}
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))) U)]
variable [∀ U : (RingedSite.ofCommRingSheaf (ProEt.topology X)
      (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))).carrier,
  PreservesFiniteColimits
    (localizedRestriction.{v}
      (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X (Λ ⧸ I ^ (1 : ℕ)))) U)]
variable [∀ U : X.ProEt, HasWeakSheafify ((ProEt.topology X).over U) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ))),
  (ProEt.baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{v} (Λ ⧸ I ^ (1 : ℕ)))]


/-- An object of `D(X_proétale, Λ)` is constructible with respect to `I` when it is derived
complete with respect to `I` and the reduction `K ⊗ᴸ underline{Λ / I}` has constructible
cohomology sheaves and locally has finite Tor dimension. -/
class IsConstructible (K : ProetaleDerived X Λ) : Prop where
  /-- `K` is derived complete with respect to `I`. -/
  derivedComplete : IsDerivedCompleteWithRespectTo K I
  /-- The reduction has constructible cohomology sheaves. -/
  reduction_cohomologyIn :
    DerivedCategory.cohomologyIn constructibleModule (proEtReduction I 1 K)
  /-- The quotient-coefficient reduction locally has finite Tor dimension over Λ / I. -/
  reduction_locallyHasFiniteTorDimension :
    locallyHasFiniteTorDimension (proEtReduction I 1 K)

/-- Constructibility is equivalent to derived completeness, constructible cohomology of the
reduction, and local finite Tor dimension of the transported reduction. -/
theorem isConstructible_iff (K : ProetaleDerived X Λ) :
    IsConstructible I K ↔
      IsDerivedCompleteWithRespectTo K I ∧
        DerivedCategory.cohomologyIn constructibleModule (proEtReduction I 1 K) ∧
          locallyHasFiniteTorDimension (proEtReduction I 1 K) := sorry

/-- The three defining conditions of constructibility. -/
theorem IsConstructible.spec (K : ProetaleDerived X Λ) [IsConstructible I K] :
    IsDerivedCompleteWithRespectTo K I ∧
      DerivedCategory.cohomologyIn constructibleModule (proEtReduction I 1 K) ∧
        locallyHasFiniteTorDimension (proEtReduction I 1 K) := sorry

/-- The zero object of `D(X_proétale, Λ)` is constructible. -/
instance instIsConstructible_zero :
    IsConstructible I (0 : ProetaleDerived X Λ) := sorry

/-- The object property on `D(X_proétale, Λ)` selecting complexes constructible with respect to
`I`. -/
def constructibleObjectProperty :
    ObjectProperty (ProetaleDerived X Λ) :=
  fun K ↦ IsConstructible I K

/-- Membership in `constructibleObjectProperty` is the constructibility predicate. -/
theorem constructibleObjectProperty_apply (K : ProetaleDerived X Λ) :
    constructibleObjectProperty I K ↔ IsConstructible I K := sorry

variable (X)

/-- The full subcategory `D_cons(X, Λ)` of constructible objects in `D(X_proétale, Λ)`. -/
abbrev ProetaleConstructible :=
  (constructibleObjectProperty I : ObjectProperty (ProetaleDerived X Λ)).FullSubcategory

/-- An object of `D_cons(X, Λ)` is a constructible object of `D(X_proétale, Λ)`. -/
def ProetaleConstructible.mk (K : ProetaleDerived X Λ)
    (h : IsConstructible I K) :
    ProetaleConstructible X I :=
  ⟨K, h⟩

/-- An object of `D_cons(X, Λ)` is a constructible object of `D(X_proétale, Λ)`. -/
theorem ProetaleConstructible.mem_iff 
    (K : ProetaleConstructible X I) :
    IsConstructible I K.obj := sorry

end AlgebraicGeometry.Scheme.ProetaleDerived
