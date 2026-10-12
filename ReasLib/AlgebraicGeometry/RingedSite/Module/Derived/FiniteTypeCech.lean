/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExtendedCech
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Presentation

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.ExtendedCech

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}} {r : ℕ}

/-- The extended alternating Čech complex of a finite family of sections, viewed in the
derived category of sheaves of modules. -/
noncomputable abbrev derived
    (f : Fin r → (unitModule J O).sections) : RingedSiteDerived J O :=
  (@CochainComplex.Nat.toDerived _ _
    (moduleCategoryAbelian (J := J) (𝒪 := O))
    (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).obj (complex f)

/-- The derived Čech object is the derived realization of the explicit nonnegative complex. -/
theorem derived_eq (f : Fin r → (unitModule J O).sections) :
    derived f =
      (@CochainComplex.Nat.toDerived _ _
        (moduleCategoryAbelian (J := J) (𝒪 := O))
        (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).obj (complex f) := sorry

/-- The projection from the extended alternating Čech object to the structure module in degree
zero. -/
noncomputable def projection
    (f : Fin r → (unitModule J O).sections) :
    derived f ⟶
      (@DerivedCategory.singleFunctor _ _
        (moduleCategoryAbelian (J := J) (𝒪 := O))
        (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O)) (0 : ℤ)).obj
        (unitModule J O) :=
  (@DerivedCategory.Q _ _
      (moduleCategoryAbelian (J := J) (𝒪 := O))
      (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).map
      ((HomologicalComplex.extendMap
        ((CochainComplex.toSingle₀Equiv (complex f) (unitModule J O)).symm
          (𝟙 (unitModule J O))) ComplexShape.embeddingUpNat) ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
          (unitModule J O) (0 : ℕ) (0 : ℤ) rfl).hom) ≫
    ((@DerivedCategory.singleFunctorIsoCompQ _ _
      (moduleCategoryAbelian (J := J) (𝒪 := O))
      (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O)) (0 : ℤ)).app
      (unitModule J O)).symm.hom

/-- The derived Čech projection is induced by the identity on its degree-zero structure-module
term and zero in every other degree. -/
theorem projection_eq (f : Fin r → (unitModule J O).sections) :
    projection f =
      (@DerivedCategory.Q _ _
        (moduleCategoryAbelian (J := J) (𝒪 := O))
        (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).map
        ((HomologicalComplex.extendMap
          ((CochainComplex.toSingle₀Equiv (complex f) (unitModule J O)).symm
            (𝟙 (unitModule J O))) ComplexShape.embeddingUpNat) ≫
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
            (unitModule J O) (0 : ℕ) (0 : ℤ) rfl).hom) ≫
      ((@DerivedCategory.singleFunctorIsoCompQ _ _
        (moduleCategoryAbelian (J := J) (𝒪 := O))
        (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O)) (0 : ℤ)).app
        (unitModule J O)).symm.hom := sorry

end SheafOfModules.RingedSite.ExtendedCech

namespace RingedSite.Hom.ModuleDerived

open SheafOfModules.RingedSite.ExtendedCech

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- Restrict a derived map to the structure module and compare its target with the local
structure module in degree zero. -/
noncomputable def localizedMapToUnit (U : C) {K : RingedSiteDerived J O}
    (eta : K ⟶
      (@DerivedCategory.singleFunctor _ _
        (moduleCategoryAbelian (J := J) (𝒪 := O))
        (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O)) (0 : ℤ)).obj
        (unitModule J O)) :
    (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).obj K ⟶
      (@DerivedCategory.singleFunctor _ _
        (moduleCategoryAbelian (J := J.over U) (𝒪 := O.over U))
        (moduleCategoryHasDerivedCategory (J := J.over U) (𝒪 := O.over U)) (0 : ℤ)).obj
          (unitModule (J.over U) (O.over U)) :=
  (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).map eta ≫
    ((@CategoryTheory.Functor.mapDerivedCategorySingleFunctor
      _ _ _ (RingedSite.Hom.moduleCat_hasDerivedCategory
        (RingedSite.ofCommRingSheaf J O))
      _ _ (RingedSite.moduleCatAbelian
        ((RingedSite.ofCommRingSheaf J O).localization U))
      (RingedSite.Hom.moduleCat_hasDerivedCategory
        ((RingedSite.ofCommRingSheaf J O).localization U))
      (localizedRestriction.{u} (RingedSite.ofCommRingSheaf J O) U)
      (localizedRestriction_additive (RingedSite.ofCommRingSheaf J O) U)
      (localizedRestriction_preservesFiniteLimits (RingedSite.ofCommRingSheaf J O) U)
      (localizedRestriction_preservesFiniteColimits (RingedSite.ofCommRingSheaf J O) U)
      (0 : ℤ)).hom.app (unitModule J O))

/-- The localized map to the structure module is the derived restricted map followed by the
canonical comparison with the local degree-zero structure module. -/
theorem localizedMapToUnit_eq (U : C) {K : RingedSiteDerived J O}
    (eta : K ⟶
      (@DerivedCategory.singleFunctor _ _
        (moduleCategoryAbelian (J := J) (𝒪 := O))
        (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O)) (0 : ℤ)).obj
        (unitModule J O)) :
    localizedMapToUnit U eta =
      (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).map eta ≫
        ((@CategoryTheory.Functor.mapDerivedCategorySingleFunctor
          _ _ _ (RingedSite.Hom.moduleCat_hasDerivedCategory
            (RingedSite.ofCommRingSheaf J O))
          _ _ (RingedSite.moduleCatAbelian
            ((RingedSite.ofCommRingSheaf J O).localization U))
          (RingedSite.Hom.moduleCat_hasDerivedCategory
            ((RingedSite.ofCommRingSheaf J O).localization U))
          (localizedRestriction.{u} (RingedSite.ofCommRingSheaf J O) U)
          (localizedRestriction_additive (RingedSite.ofCommRingSheaf J O) U)
          (localizedRestriction_preservesFiniteLimits (RingedSite.ofCommRingSheaf J O) U)
          (localizedRestriction_preservesFiniteColimits (RingedSite.ofCommRingSheaf J O) U)
          (0 : ℤ)).hom.app (unitModule J O)) := sorry

/-- A finite-type ideal sheaf admits a derived Čech object mapping to the structure sheaf.
On every slice where a finite family generates the restricted ideal sheaf, this object
restricts to the corresponding extended alternating Čech complex, compatibly with the
projections to the local structure sheaf. -/
theorem existsCechModelOfFiniteType
      (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :
    ∃ (K : RingedSiteDerived J O)
      (η : K ⟶
        (@DerivedCategory.singleFunctor _ _
          (moduleCategoryAbelian (J := J) (𝒪 := O))
          (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O)) (0 : ℤ)).obj
          (unitModule J O)),
      ∀ (U : C) (r : ℕ)
        (f : Fin r → (unitModule (J.over U) (O.over U)).sections),
        generatedIdeal f = imageSubobject (I.arrow.over U) →
          ∃ e : derived f ≅
              (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).obj K,
            e.hom ≫ localizedMapToUnit U η = projection f := sorry

end RingedSite.Hom.ModuleDerived
