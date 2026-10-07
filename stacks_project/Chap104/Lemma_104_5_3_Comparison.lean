module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Shift.Adjunction
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization.Exact
public import stacks_project.Chap103.Lemma_103_14_4_LowerShriek
public import stacks_project.Chap104.Lemma_104_5_2_Comparison
public import stacks_project.Chap104.Lemma_104_5_3_DerivedQCoh

/-!
# Derived inverse image and lower shriek on quasi-coherent complexes

The lisse-étale and flat-fppf inclusions of Lemma 103.14.2 give exact module
inverse image `g^* = g⁻¹`. Passing to derived categories, restricting to
`D_{LQCoh^{fbc}}` and `D_QCoh` of the small sites, and factoring through the
parasitic Verdier quotient produces mutually inverse functors between
`D_QCoh(𝒪_X)` and small-site `D_QCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Limits CategoryTheory.ObjectProperty
open ComplexShape RingedSite.Cocontinuous
open CategoryTheory.Adjunction.TotalDerived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Lisse-étale module inverse image is additive. -/
instance lisseEtaleModuleInverseImage.instAdditive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleModuleInverseImage X).Additive :=
  sorry

/-- Lisse-étale module inverse image preserves finite limits. -/
instance lisseEtaleModuleInverseImage.preservesFiniteLimits
    (X : GroupoidsOver S) [AlgebraicStack X] :
    PreservesFiniteLimits (lisseEtaleModuleInverseImage X) :=
  sorry

/-- Lisse-étale module inverse image preserves finite colimits. -/
instance lisseEtaleModuleInverseImage.preservesFiniteColimits
    (X : GroupoidsOver S) [AlgebraicStack X] :
    PreservesFiniteColimits (lisseEtaleModuleInverseImage X) :=
  sorry

/-- Bundled exact underived inverse image along the lisse-étale inclusion. -/
abbrev lisseEtaleModuleInverseImage.exact (X : GroupoidsOver S)
    [AlgebraicStack X] :
    etaleModules X ⥤ₑ SheafOfModules.{u} (lisseEtaleStructureSheaf X) :=
  ExactFunctor.of (lisseEtaleModuleInverseImage X)

/-- `lisseEtaleModuleInverseImage.exact` is `ExactFunctor.of` of underived
inverse image. -/
theorem lisseEtaleModuleInverseImage.exact_eq (X : GroupoidsOver S)
    [AlgebraicStack X] :
    lisseEtaleModuleInverseImage.exact X =
      ExactFunctor.of (lisseEtaleModuleInverseImage X) :=
  sorry

namespace lisseEtaleModuleInverseImage

/-- Derived inverse image `g^* : D(X_étale, 𝒪_X) ⥤ D(𝒪_{X_lisse,étale})`. -/
abbrev derived (X : GroupoidsOver S) [AlgebraicStack X] :
    ModuleDerivedEtale X ⥤ ModuleDerivedLisseEtale X :=
  ExactFunctor.mapDerivedCategory (exact X)

/-- Derived lisse-étale inverse image is `mapDerivedCategory` of the bundled
exact underived functor. -/
theorem derived_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    derived X = ExactFunctor.mapDerivedCategory (exact X) :=
  sorry

/-- Derived lisse-étale inverse image commutes with shifts. -/
instance derived.instCommShift (X : GroupoidsOver S) [AlgebraicStack X] :
    (derived X).CommShift ℤ :=
  inferInstance

/-- Derived lisse-étale inverse image is a triangulated functor. -/
instance derived.instIsTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derived X).IsTriangulated :=
  inferInstance

end lisseEtaleModuleInverseImage

/-- Derived `g^*` sends étale `LQCoh^{fbc}` cohomology into lisse-étale
quasi-coherent cohomology. -/
theorem lisseEtaleInverseImageDerived_maps_qcoh (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedCategory.cohomologyIn (lqcohFbc X) ≤
      (DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X))).inverseImage
        (lisseEtaleModuleInverseImage.derived X) :=
  sorry

/-- Restricted derived inverse image
`g^* : D_{LQCoh^{fbc}}(X_étale, 𝒪_X) ⥤ D_QCoh(𝒪_{X_lisse,étale})`. -/
abbrev lisseEtaleInverseImageDerivedLQCohFbc (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedLQCohFbcEtale X ⥤ DerivedQCohLisseEtale X :=
  FullSubcategory.restrict (lisseEtaleModuleInverseImage.derived X)
    (lisseEtaleInverseImageDerived_maps_qcoh X)

/-- Restriction of derived lisse-étale `g^*` whiskers with the inclusions to
the unrestricted derived functor. -/
abbrev lisseEtaleInverseImageDerivedLQCohFbc_comp_inclusion
    (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleInverseImageDerivedLQCohFbc X ⋙
        DerivedQCohLisseEtale.inclusion X ≅
      DerivedLQCohFbcEtale.inclusion X ⋙
        lisseEtaleModuleInverseImage.derived X :=
  FullSubcategory.restrict.compιIso (lisseEtaleModuleInverseImage.derived X)
    (lisseEtaleInverseImageDerived_maps_qcoh X)

/-- Restricted derived lisse-étale `g^*` commutes with shifts. -/
instance lisseEtaleInverseImageDerivedLQCohFbc.instCommShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInverseImageDerivedLQCohFbc X).CommShift ℤ :=
  Functor.CommShift.ofComp
    (lisseEtaleInverseImageDerivedLQCohFbc_comp_inclusion X) ℤ

/-- Restricted derived lisse-étale `g^*` is triangulated. -/
instance lisseEtaleInverseImageDerivedLQCohFbc.instIsTriangulated
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInverseImageDerivedLQCohFbc X).IsTriangulated :=
  sorry

/-- Derived `g^*` of an étale `D_{LQCoh^{fbc}}` object vanishes iff the object
has parasitic cohomology. Here `P_X` is `derivedParasiticEtale`. -/
theorem lisseEtaleInverseImageDerived_isZero_iff_derivedParasitic
    {X : GroupoidsOver S} [AlgebraicStack X] (F : DerivedLQCohFbcEtale X) :
    IsZero ((lisseEtaleModuleInverseImage.derived X).obj
        ((DerivedLQCohFbcEtale.inclusion X).obj F)) ↔
      derivedParasiticEtale X F :=
  sorry

/-- Lisse-étale module lower shriek is additive. Named separately from
`lisseEtaleModuleLowerShriek.instAdditive` in Lemma 104.3.3 because that file
cannot be imported with `Lemma_104_5_2_Comparison` (`projection_isContinuous`
diamond). -/
instance derivedLisseEtaleLowerShriek.additive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleModuleLowerShriek X).Additive :=
  moduleLowerShriek.additive (lisseEtaleInclusion X) (etaleStructureSheaf X)

namespace derivedLisseEtaleLowerShriek

/-- Homotopy-to-derived presentation of lisse-étale module lower shriek.
U-level twin of `lisseEtaleModuleLowerShriek.toDerived` from Lemma 104.3.3. -/
abbrev toDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    HomotopyCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ) ⥤
      ModuleDerivedEtale X :=
  (lisseEtaleModuleLowerShriek X).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- The homotopy-to-derived lisse-étale module lower shriek has a total left
derived functor. -/
instance toDerived.hasLeftDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.HasLeftDerivedFunctor (toDerived X)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ)) :=
  sorry

end derivedLisseEtaleLowerShriek

/-- Derived module lower shriek from the lisse-étale site to
`D(X_étale, 𝒪_X)`. U-level twin of `lisseEtaleModuleLowerShriek.derived` from
Lemma 104.3.3, which cannot be imported with `Lemma_104_5_2_Comparison`. -/
abbrev derivedLisseEtaleLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) ⥤
      ModuleDerivedEtale X :=
  Functor.totalLeftDerived (derivedLisseEtaleLowerShriek.toDerived X)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ))

/-- Derived `Lg_!` sends lisse-étale quasi-coherent cohomology into étale
`LQCoh^{fbc}` cohomology. -/
theorem lisseEtaleLowerShriekDerived_maps_lqcohFbc (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X)) ≤
      (DerivedCategory.cohomologyIn (lqcohFbc X)).inverseImage
        (derivedLisseEtaleLowerShriek X) :=
  sorry

/-- Restricted derived lower shriek
`Lg_! : D_QCoh(𝒪_{X_lisse,étale}) ⥤ D_{LQCoh^{fbc}}(X_étale, 𝒪_X)`. -/
abbrev lisseEtaleLowerShriekDerivedQCoh (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedQCohLisseEtale X ⥤ DerivedLQCohFbcEtale X :=
  FullSubcategory.restrict (derivedLisseEtaleLowerShriek X)
    (lisseEtaleLowerShriekDerived_maps_lqcohFbc X)

/-- Restriction of derived lisse-étale `Lg_!` whiskers with the inclusions to
the unrestricted derived functor. -/
abbrev lisseEtaleLowerShriekDerivedQCoh_comp_inclusion
    (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleLowerShriekDerivedQCoh X ⋙ DerivedLQCohFbcEtale.inclusion X ≅
      DerivedQCohLisseEtale.inclusion X ⋙
        derivedLisseEtaleLowerShriek X :=
  FullSubcategory.restrict.compιIso (derivedLisseEtaleLowerShriek X)
    (lisseEtaleLowerShriekDerived_maps_lqcohFbc X)

/-- Homotopy-to-derived lisse-étale inverse image has a total right-derived
functor. -/
instance lisseEtaleModuleInverseImage.toDerived.hasRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ((lisseEtaleModuleInverseImage X).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (etaleModules X) (up ℤ)) :=
  sorry

/-- Exact derived lisse-étale inverse image is a right-derived functor of its
homotopy presentation. -/
instance lisseEtaleModuleInverseImage.derived.isRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleModuleInverseImage.derived X).IsRightDerivedFunctor
      (lisseEtaleModuleInverseImage X).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (etaleModules X) (up ℤ)) :=
  sorry

/-- The homotopy lisse-étale lower-shriek/inverse-image adjunction satisfies
the absolute total-derived pair condition. -/
instance derivedLisseEtaleLowerShriek.hasPair
    (X : GroupoidsOver S) [AlgebraicStack X] :
    HasPair
      (G := (lisseEtaleModuleLowerShriek X).mapHomotopyCategory (up ℤ))
      (F := (lisseEtaleModuleInverseImage X).mapHomotopyCategory (up ℤ))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ))
      (HomotopyCategory.quasiIso (etaleModules X) (up ℤ))
      (L1 := DerivedCategory.Qh)
      (L2 := DerivedCategory.Qh) :=
  sorry

/-- The total-right-derived lisse-étale inverse image agrees with exact
derived inverse image. -/
def lisseEtaleModuleInverseImage.totalDerivedIso
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ((lisseEtaleModuleInverseImage X).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (etaleModules X) (up ℤ)) ≅
      lisseEtaleModuleInverseImage.derived X :=
  Functor.rightDerivedNatIso
    (((lisseEtaleModuleInverseImage X).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (etaleModules X) (up ℤ)))
    (lisseEtaleModuleInverseImage.derived X)
    (((lisseEtaleModuleInverseImage X).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (etaleModules X) (up ℤ)))
    (lisseEtaleModuleInverseImage X).mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso (etaleModules X) (up ℤ))
    (Iso.refl _)

/-- Derived lisse-étale `Lg_!` is left adjoint to exact derived inverse
image. -/
def derivedLisseEtaleLowerShriek.adjunction
    (X : GroupoidsOver S) [AlgebraicStack X] :
    derivedLisseEtaleLowerShriek X ⊣
      lisseEtaleModuleInverseImage.derived X :=
  (HasPair.derived
      (Adjunction.mapHomotopyCategoryAdjunction
        (lisseEtaleModuleLowerShriek.adjunction X))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) (up ℤ))
      (HomotopyCategory.quasiIso (etaleModules X) (up ℤ))).ofNatIsoRight
    (lisseEtaleModuleInverseImage.totalDerivedIso X)

/-- Restricted derived lisse-étale `Lg_!` is left adjoint to restricted
derived inverse image. -/
def lisseEtaleLowerShriekDerivedQCoh.adjunction
    (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleLowerShriekDerivedQCoh X ⊣
      lisseEtaleInverseImageDerivedLQCohFbc X :=
  FullSubcategory.adjunction
    (derivedLisseEtaleLowerShriek X)
    (lisseEtaleModuleInverseImage.derived X)
    (derivedLisseEtaleLowerShriek.adjunction X)
    (lisseEtaleLowerShriekDerived_maps_lqcohFbc X)
    (lisseEtaleInverseImageDerived_maps_qcoh X)

/-- Restricted derived lisse-étale `g^*` inverts the étale parasitic Verdier
system. -/
theorem lisseEtaleInverseImageDerivedLQCohFbc_inverts
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (derivedParasiticEtale X).trW.IsInvertedBy
      (lisseEtaleInverseImageDerivedLQCohFbc X) :=
  sorry

/-- Induced functor on the étale Verdier quotient
`g^* : D_{LQCoh^{fbc}}(X_étale, 𝒪_X) / D_{P_X} ⥤ D_QCoh(𝒪_{X_lisse,étale})`. -/
abbrev lisseEtaleDerivedQCohEtaleInverseImage (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedQCohEtale X ⥤ DerivedQCohLisseEtale X :=
  VerdierQuotient.Exact.factor (derivedParasiticEtale X)
    (lisseEtaleInverseImageDerivedLQCohFbc X)
    (lisseEtaleInverseImageDerivedLQCohFbc_inverts X)

/-- Canonical comparison from the étale quotient functor followed by induced
étale `g^*` to restricted derived inverse image. -/
abbrev lisseEtaleDerivedQCohEtaleInverseImage_facIso
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (derivedParasiticEtale X).trW.Q ⋙
        lisseEtaleDerivedQCohEtaleInverseImage X ≅
      lisseEtaleInverseImageDerivedLQCohFbc X :=
  VerdierQuotient.Exact.factor.facIso (derivedParasiticEtale X)
    (lisseEtaleInverseImageDerivedLQCohFbc X)
    (lisseEtaleInverseImageDerivedLQCohFbc_inverts X)

/-- The étale induced `g^*` strictly factors restricted derived inverse
image. -/
theorem lisseEtaleDerivedQCohEtaleInverseImage_fac (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasiticEtale X).trW.Q ⋙
        lisseEtaleDerivedQCohEtaleInverseImage X =
      lisseEtaleInverseImageDerivedLQCohFbc X :=
  sorry

/-- Induced étale `g^*` commutes with shifts. -/
instance lisseEtaleDerivedQCohEtaleInverseImage.instCommShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleDerivedQCohEtaleInverseImage X).CommShift ℤ :=
  VerdierQuotient.Exact.factor.commShift (derivedParasiticEtale X)
    (lisseEtaleInverseImageDerivedLQCohFbc X)
    (lisseEtaleInverseImageDerivedLQCohFbc_inverts X)

/-- Induced étale `g^*` is triangulated. -/
instance lisseEtaleDerivedQCohEtaleInverseImage.instIsTriangulated
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleDerivedQCohEtaleInverseImage X).IsTriangulated :=
  VerdierQuotient.Exact.factor.isTriangulated (derivedParasiticEtale X)
    (lisseEtaleInverseImageDerivedLQCohFbc X)
    (lisseEtaleInverseImageDerivedLQCohFbc_inverts X)

/-- The étale Verdier factor of derived `g^*` is an equivalence. -/
instance lisseEtaleDerivedQCohEtaleInverseImage.instIsEquivalence
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleDerivedQCohEtaleInverseImage X).IsEquivalence :=
  sorry

/-- Quasi-inverse `Lg_!` from lisse-étale `D_QCoh` to the étale Verdier
quotient, as restricted `Lg_!` followed by the étale quotient functor. -/
abbrev lisseEtaleDerivedQCohEtaleLowerShriek (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedQCohLisseEtale X ⥤ DerivedQCohEtale X :=
  lisseEtaleLowerShriekDerivedQCoh X ⋙
    DerivedQCohEtale.quotientFunctor X

/-- Restricted `Lg_!` commutes with the étale quotient functor. -/
instance lisseEtaleDerivedQCohEtale_catCommSq_lowerShriek
    (X : GroupoidsOver S) [AlgebraicStack X] :
    CatCommSq (lisseEtaleLowerShriekDerivedQCoh X)
      (𝟭 (DerivedQCohLisseEtale X))
      (DerivedQCohEtale.quotientFunctor X)
      (lisseEtaleDerivedQCohEtaleLowerShriek X) where
  iso := (Functor.leftUnitor _).symm

/-- Restricted `g^*` commutes with the étale quotient functor. -/
instance lisseEtaleDerivedQCohEtale_catCommSq_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] :
    CatCommSq (lisseEtaleInverseImageDerivedLQCohFbc X)
      (DerivedQCohEtale.quotientFunctor X)
      (𝟭 (DerivedQCohLisseEtale X))
      (lisseEtaleDerivedQCohEtaleInverseImage X) where
  iso := Functor.rightUnitor _ ≪≫
    (lisseEtaleDerivedQCohEtaleInverseImage_facIso X).symm

/-- Induced adjunction on the étale Verdier quotient
`Lg_! ⊣ g^*` between lisse-étale `D_QCoh` and `D_QCoh` of the associated
étale site. -/
def lisseEtaleDerivedQCohEtaleLowerShriek.adjunction
    (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleDerivedQCohEtaleLowerShriek X ⊣
      lisseEtaleDerivedQCohEtaleInverseImage X :=
  (lisseEtaleLowerShriekDerivedQCoh.adjunction X).localization
    (𝟭 (DerivedQCohLisseEtale X))
    (MorphismProperty.isomorphisms (DerivedQCohLisseEtale X))
    (DerivedQCohEtale.quotientFunctor X)
    (derivedParasiticEtale X).trW
    (lisseEtaleDerivedQCohEtaleLowerShriek X)
    (lisseEtaleDerivedQCohEtaleInverseImage X)

/-- Derived inverse image `g^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{X_lisse,étale})`,
obtained by transporting the étale Verdier factor along
`etaleFppfInverseImageDerivedQCoh`. -/
abbrev lisseEtaleDerivedQCohInverseImage (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedQCoh X ⥤ DerivedQCohLisseEtale X :=
  (etaleFppfInverseImageDerivedQCoh X).inv ⋙
    lisseEtaleDerivedQCohEtaleInverseImage X

/-- `asEquivalence` of étale–fppf derived `ε^*` inherits shift commutation. -/
instance etaleFppfInverseImageDerivedQCoh_equivalenceFunctor_commShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (Functor.asEquivalence (etaleFppfInverseImageDerivedQCoh X)).functor.CommShift ℤ :=
  inferInstanceAs ((etaleFppfInverseImageDerivedQCoh X).CommShift ℤ)

/-- Inverse of étale–fppf derived `ε^*` on `D_QCoh` commutes with shifts. -/
instance etaleFppfInverseImageDerivedQCoh_inv_commShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ((etaleFppfInverseImageDerivedQCoh X).inv).CommShift ℤ :=
  Equivalence.commShiftInverse
    (Functor.asEquivalence (etaleFppfInverseImageDerivedQCoh X)) ℤ

/-- Transported derived `g^*` commutes with shifts. -/
instance lisseEtaleDerivedQCohInverseImage.instCommShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleDerivedQCohInverseImage X).CommShift ℤ :=
  inferInstance

/-- Transported derived `g^*` is triangulated. -/
instance lisseEtaleDerivedQCohInverseImage.instIsTriangulated
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleDerivedQCohInverseImage X).IsTriangulated :=
  sorry

/-- Quasi-inverse `Lg_! : D_QCoh(𝒪_{X_lisse,étale}) ⥤ D_QCoh(𝒪_X)`, as
restricted `Lg_!` followed by the étale quotient functor and then
`etaleFppfInverseImageDerivedQCoh`. -/
abbrev lisseEtaleDerivedQCohLowerShriek (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedQCohLisseEtale X ⥤ DerivedQCoh X :=
  lisseEtaleDerivedQCohEtaleLowerShriek X ⋙
    etaleFppfInverseImageDerivedQCoh X

/-- Transported adjunction `Lg_! ⊣ g^*` between `D_QCoh(𝒪_X)` and lisse-étale
`D_QCoh`, conjugating the étale pair by `etaleFppfInverseImageDerivedQCoh`. -/
def lisseEtaleDerivedQCohLowerShriek.adjunction
    (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleDerivedQCohLowerShriek X ⊣
      lisseEtaleDerivedQCohInverseImage X :=
  (lisseEtaleDerivedQCohEtaleLowerShriek.adjunction X).comp
    (Functor.asEquivalence (etaleFppfInverseImageDerivedQCoh X)).toAdjunction

/-- The unit `id ⟶ Lg_! ⋙ g^*` is an isomorphism on lisse-étale `D_QCoh`. -/
instance lisseEtaleDerivedQCohLowerShriek_unit_app_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] (H : DerivedQCohLisseEtale X) :
    IsIso ((lisseEtaleDerivedQCohLowerShriek.adjunction X).unit.app H) :=
  sorry

/-- The counit `g^* ⋙ Lg_! ⟶ id` is an isomorphism on `D_QCoh(𝒪_X)`. -/
instance lisseEtaleDerivedQCohLowerShriek_counit_app_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] (E : DerivedQCoh X) :
    IsIso ((lisseEtaleDerivedQCohLowerShriek.adjunction X).counit.app E) :=
  sorry

/-- Composite of induced `g^*` with the `Lg_!` quasi-inverse is naturally
isomorphic to the identity on `D_QCoh(𝒪_X)`. -/
def lisseEtaleDerivedQCohInverseImage_comp_lowerShriek
    (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleDerivedQCohInverseImage X ⋙
        lisseEtaleDerivedQCohLowerShriek X ≅
      𝟭 (DerivedQCoh X) :=
  NatIso.ofComponents
    (fun E ↦ asIso
      ((lisseEtaleDerivedQCohLowerShriek.adjunction X).counit.app E))
    sorry

/-- Composite of the `Lg_!` quasi-inverse with induced `g^*` is naturally
isomorphic to the identity on lisse-étale `D_QCoh`. -/
def lisseEtaleDerivedQCohLowerShriek_comp_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleDerivedQCohLowerShriek X ⋙
        lisseEtaleDerivedQCohInverseImage X ≅
      𝟭 (DerivedQCohLisseEtale X) :=
  NatIso.ofComponents
    (fun H ↦
      (asIso
          ((lisseEtaleDerivedQCohLowerShriek.adjunction X).unit.app H)).symm)
    sorry

/-- The functors `g^*` and `Lg_!` are mutually inverse between `D_QCoh(𝒪_X)`
and lisse-étale `D_QCoh`. -/
instance lisseEtaleDerivedQCohInverseImage.instIsEquivalence
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleDerivedQCohInverseImage X).IsEquivalence :=
  Functor.IsEquivalence.mk'
    (lisseEtaleDerivedQCohLowerShriek X)
    (lisseEtaleDerivedQCohInverseImage_comp_lowerShriek X).symm
    (lisseEtaleDerivedQCohLowerShriek_comp_inverseImage X)

/-- Flat-fppf module inverse image is additive. -/
instance flatFppfModuleInverseImage.instAdditive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfModuleInverseImage X).Additive :=
  sorry

/-- Flat-fppf module inverse image preserves finite limits. -/
instance flatFppfModuleInverseImage.preservesFiniteLimits
    (X : GroupoidsOver S) [AlgebraicStack X] :
    PreservesFiniteLimits (flatFppfModuleInverseImage X) :=
  sorry

/-- Flat-fppf module inverse image preserves finite colimits. -/
instance flatFppfModuleInverseImage.preservesFiniteColimits
    (X : GroupoidsOver S) [AlgebraicStack X] :
    PreservesFiniteColimits (flatFppfModuleInverseImage X) :=
  sorry

/-- Bundled exact underived inverse image along the flat-fppf inclusion. -/
abbrev flatFppfModuleInverseImage.exact (X : GroupoidsOver S)
    [AlgebraicStack X] :
    fppfModules X ⥤ₑ SheafOfModules.{u} (flatFppfStructureSheaf X) :=
  ExactFunctor.of (flatFppfModuleInverseImage X)

/-- `flatFppfModuleInverseImage.exact` is `ExactFunctor.of` of underived
inverse image. -/
theorem flatFppfModuleInverseImage.exact_eq (X : GroupoidsOver S)
    [AlgebraicStack X] :
    flatFppfModuleInverseImage.exact X =
      ExactFunctor.of (flatFppfModuleInverseImage X) :=
  sorry

namespace flatFppfModuleInverseImage

/-- Derived inverse image `g^* : D(𝒪_X) ⥤ D(𝒪_{X_flat,fppf})`. -/
abbrev derived (X : GroupoidsOver S) [AlgebraicStack X] :
    ModuleDerived X ⥤ ModuleDerivedFlatFppf X :=
  ExactFunctor.mapDerivedCategory (exact X)

/-- Derived flat-fppf inverse image is `mapDerivedCategory` of the bundled
exact underived functor. -/
theorem derived_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    derived X = ExactFunctor.mapDerivedCategory (exact X) :=
  sorry

/-- Derived flat-fppf inverse image commutes with shifts. -/
instance derived.instCommShift (X : GroupoidsOver S) [AlgebraicStack X] :
    (derived X).CommShift ℤ :=
  inferInstance

/-- Derived flat-fppf inverse image is a triangulated functor. -/
instance derived.instIsTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derived X).IsTriangulated :=
  inferInstance

end flatFppfModuleInverseImage

/-- Derived `g^*` sends fppf `LQCoh^{fbc}` cohomology into flat-fppf
quasi-coherent cohomology. -/
theorem flatFppfInverseImageDerived_maps_qcoh (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) ≤
      (DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X))).inverseImage
        (flatFppfModuleInverseImage.derived X) :=
  sorry

/-- Restricted derived inverse image
`g^* : D_{LQCoh^{fbc}}(𝒪_X) ⥤ D_QCoh(𝒪_{X_flat,fppf})`. -/
abbrev flatFppfInverseImageDerivedLQCohFbc (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedLQCohFbc X ⥤ DerivedQCohFlatFppf X :=
  FullSubcategory.restrict (flatFppfModuleInverseImage.derived X)
    (flatFppfInverseImageDerived_maps_qcoh X)

/-- Restriction of derived flat-fppf `g^*` whiskers with the inclusions to the
unrestricted derived functor. -/
abbrev flatFppfInverseImageDerivedLQCohFbc_comp_inclusion
    (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfInverseImageDerivedLQCohFbc X ⋙ DerivedQCohFlatFppf.inclusion X ≅
      DerivedLQCohFbc.inclusion X ⋙ flatFppfModuleInverseImage.derived X :=
  FullSubcategory.restrict.compιIso (flatFppfModuleInverseImage.derived X)
    (flatFppfInverseImageDerived_maps_qcoh X)

/-- Restricted derived flat-fppf `g^*` commutes with shifts. -/
instance flatFppfInverseImageDerivedLQCohFbc.instCommShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInverseImageDerivedLQCohFbc X).CommShift ℤ :=
  Functor.CommShift.ofComp
    (flatFppfInverseImageDerivedLQCohFbc_comp_inclusion X) ℤ

/-- Restricted derived flat-fppf `g^*` is triangulated. -/
instance flatFppfInverseImageDerivedLQCohFbc.instIsTriangulated
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInverseImageDerivedLQCohFbc X).IsTriangulated :=
  sorry

/-- Derived `g^*` of an fppf `D_{LQCoh^{fbc}}` object vanishes iff the object
has parasitic cohomology. Here `P_X` is `derivedParasitic`. -/
theorem flatFppfInverseImageDerived_isZero_iff_derivedParasitic
    {X : GroupoidsOver S} [AlgebraicStack X] (F : DerivedLQCohFbc X) :
    IsZero ((flatFppfModuleInverseImage.derived X).obj
        ((DerivedLQCohFbc.inclusion X).obj F)) ↔
      derivedParasitic X F :=
  sorry

/-- Flat-fppf module lower shriek is additive. Named separately from
`flatFppfModuleLowerShriek.instAdditive` in Lemma 104.3.3 because that file
cannot be imported with `Lemma_104_5_2_Comparison`. -/
instance derivedFlatFppfLowerShriek.additive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfModuleLowerShriek X).Additive :=
  moduleLowerShriek.additive (flatFppfInclusion X) (structureSheaf X)

namespace derivedFlatFppfLowerShriek

/-- Homotopy-to-derived presentation of flat-fppf module lower shriek.
U-level twin of `flatFppfModuleLowerShriek.toDerived` from Lemma 104.3.3. -/
abbrev toDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    HomotopyCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ) ⥤
      ModuleDerived X :=
  (flatFppfModuleLowerShriek X).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- The homotopy-to-derived flat-fppf module lower shriek has a total left
derived functor. -/
instance toDerived.hasLeftDerived (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.HasLeftDerivedFunctor (toDerived X)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ)) :=
  sorry

end derivedFlatFppfLowerShriek

/-- Derived module lower shriek from the flat-fppf site to `D(𝒪_X)`. U-level
twin of `flatFppfModuleLowerShriek.derived` from Lemma 104.3.3, which cannot
be imported with `Lemma_104_5_2_Comparison`. -/
abbrev derivedFlatFppfLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) ⥤
      ModuleDerived X :=
  Functor.totalLeftDerived (derivedFlatFppfLowerShriek.toDerived X)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ))

/-- Derived `Lg_!` sends flat-fppf quasi-coherent cohomology into fppf
`LQCoh^{fbc}` cohomology. -/
theorem flatFppfLowerShriekDerived_maps_lqcohFbc (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X)) ≤
      (DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X)).inverseImage
        (derivedFlatFppfLowerShriek X) :=
  sorry

/-- Restricted derived lower shriek
`Lg_! : D_QCoh(𝒪_{X_flat,fppf}) ⥤ D_{LQCoh^{fbc}}(𝒪_X)`. -/
abbrev flatFppfLowerShriekDerivedQCoh (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedQCohFlatFppf X ⥤ DerivedLQCohFbc X :=
  FullSubcategory.restrict (derivedFlatFppfLowerShriek X)
    (flatFppfLowerShriekDerived_maps_lqcohFbc X)

/-- Restriction of derived flat-fppf `Lg_!` whiskers with the inclusions to
the unrestricted derived functor. -/
abbrev flatFppfLowerShriekDerivedQCoh_comp_inclusion
    (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfLowerShriekDerivedQCoh X ⋙ DerivedLQCohFbc.inclusion X ≅
      DerivedQCohFlatFppf.inclusion X ⋙
        derivedFlatFppfLowerShriek X :=
  FullSubcategory.restrict.compιIso (derivedFlatFppfLowerShriek X)
    (flatFppfLowerShriekDerived_maps_lqcohFbc X)

/-- Homotopy-to-derived flat-fppf inverse image has a total right-derived
functor. -/
instance flatFppfModuleInverseImage.toDerived.hasRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ((flatFppfModuleInverseImage X).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (fppfModules X) (up ℤ)) :=
  sorry

/-- Exact derived flat-fppf inverse image is a right-derived functor of its
homotopy presentation. -/
instance flatFppfModuleInverseImage.derived.isRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfModuleInverseImage.derived X).IsRightDerivedFunctor
      (flatFppfModuleInverseImage X).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (fppfModules X) (up ℤ)) :=
  sorry

/-- The homotopy flat-fppf lower-shriek/inverse-image adjunction satisfies the
absolute total-derived pair condition. -/
instance derivedFlatFppfLowerShriek.hasPair
    (X : GroupoidsOver S) [AlgebraicStack X] :
    HasPair
      (G := (flatFppfModuleLowerShriek X).mapHomotopyCategory (up ℤ))
      (F := (flatFppfModuleInverseImage X).mapHomotopyCategory (up ℤ))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ))
      (HomotopyCategory.quasiIso (fppfModules X) (up ℤ))
      (L1 := DerivedCategory.Qh)
      (L2 := DerivedCategory.Qh) :=
  sorry

/-- The total-right-derived flat-fppf inverse image agrees with exact derived
inverse image. -/
def flatFppfModuleInverseImage.totalDerivedIso
    (X : GroupoidsOver S) [AlgebraicStack X] :
    ((flatFppfModuleInverseImage X).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (fppfModules X) (up ℤ)) ≅
      flatFppfModuleInverseImage.derived X :=
  Functor.rightDerivedNatIso
    (((flatFppfModuleInverseImage X).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (fppfModules X) (up ℤ)))
    (flatFppfModuleInverseImage.derived X)
    (((flatFppfModuleInverseImage X).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (fppfModules X) (up ℤ)))
    (flatFppfModuleInverseImage X).mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso (fppfModules X) (up ℤ))
    (Iso.refl _)

/-- Derived flat-fppf `Lg_!` is left adjoint to exact derived inverse image. -/
def derivedFlatFppfLowerShriek.adjunction
    (X : GroupoidsOver S) [AlgebraicStack X] :
    derivedFlatFppfLowerShriek X ⊣
      flatFppfModuleInverseImage.derived X :=
  (HasPair.derived
      (Adjunction.mapHomotopyCategoryAdjunction
        (flatFppfModuleLowerShriek.adjunction X))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (flatFppfStructureSheaf X)) (up ℤ))
      (HomotopyCategory.quasiIso (fppfModules X) (up ℤ))).ofNatIsoRight
    (flatFppfModuleInverseImage.totalDerivedIso X)

/-- Restricted derived flat-fppf `Lg_!` is left adjoint to restricted derived
inverse image. -/
def flatFppfLowerShriekDerivedQCoh.adjunction
    (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfLowerShriekDerivedQCoh X ⊣
      flatFppfInverseImageDerivedLQCohFbc X :=
  FullSubcategory.adjunction
    (derivedFlatFppfLowerShriek X)
    (flatFppfModuleInverseImage.derived X)
    (derivedFlatFppfLowerShriek.adjunction X)
    (flatFppfLowerShriekDerived_maps_lqcohFbc X)
    (flatFppfInverseImageDerived_maps_qcoh X)

/-- Restricted derived flat-fppf `g^*` inverts the parasitic Verdier system. -/
theorem flatFppfInverseImageDerivedLQCohFbc_inverts
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (derivedParasitic X).trW.IsInvertedBy
      (flatFppfInverseImageDerivedLQCohFbc X) :=
  sorry

/-- Induced functor on the fppf Verdier quotient
`g^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{X_flat,fppf})`. -/
abbrev flatFppfDerivedQCohInverseImage (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedQCoh X ⥤ DerivedQCohFlatFppf X :=
  VerdierQuotient.Exact.factor (derivedParasitic X)
    (flatFppfInverseImageDerivedLQCohFbc X)
    (flatFppfInverseImageDerivedLQCohFbc_inverts X)

/-- Canonical comparison from the fppf quotient functor followed by induced
`g^*` to restricted derived inverse image. -/
abbrev flatFppfDerivedQCohInverseImage_facIso (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasitic X).trW.Q ⋙ flatFppfDerivedQCohInverseImage X ≅
      flatFppfInverseImageDerivedLQCohFbc X :=
  VerdierQuotient.Exact.factor.facIso (derivedParasitic X)
    (flatFppfInverseImageDerivedLQCohFbc X)
    (flatFppfInverseImageDerivedLQCohFbc_inverts X)

/-- The induced `g^*` strictly factors restricted derived inverse image. -/
theorem flatFppfDerivedQCohInverseImage_fac (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasitic X).trW.Q ⋙ flatFppfDerivedQCohInverseImage X =
      flatFppfInverseImageDerivedLQCohFbc X :=
  sorry

/-- Induced flat-fppf `g^*` commutes with shifts. -/
instance flatFppfDerivedQCohInverseImage.instCommShift
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfDerivedQCohInverseImage X).CommShift ℤ :=
  VerdierQuotient.Exact.factor.commShift (derivedParasitic X)
    (flatFppfInverseImageDerivedLQCohFbc X)
    (flatFppfInverseImageDerivedLQCohFbc_inverts X)

/-- Induced flat-fppf `g^*` is triangulated. -/
instance flatFppfDerivedQCohInverseImage.instIsTriangulated
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfDerivedQCohInverseImage X).IsTriangulated :=
  VerdierQuotient.Exact.factor.isTriangulated (derivedParasitic X)
    (flatFppfInverseImageDerivedLQCohFbc X)
    (flatFppfInverseImageDerivedLQCohFbc_inverts X)

/-- Quasi-inverse `Lg_!` from flat-fppf `D_QCoh` to `D_QCoh(𝒪_X)`, as
restricted `Lg_!` followed by the fppf quotient functor. -/
abbrev flatFppfDerivedQCohLowerShriek (X : GroupoidsOver S)
    [AlgebraicStack X] :
    DerivedQCohFlatFppf X ⥤ DerivedQCoh X :=
  flatFppfLowerShriekDerivedQCoh X ⋙ DerivedQCoh.quotientFunctor X

/-- Restricted `Lg_!` commutes with the fppf quotient functor. -/
instance flatFppfDerivedQCoh_catCommSq_lowerShriek
    (X : GroupoidsOver S) [AlgebraicStack X] :
    CatCommSq (flatFppfLowerShriekDerivedQCoh X)
      (𝟭 (DerivedQCohFlatFppf X))
      (DerivedQCoh.quotientFunctor X)
      (flatFppfDerivedQCohLowerShriek X) where
  iso := (Functor.leftUnitor _).symm

/-- Restricted `g^*` commutes with the fppf quotient functor. -/
instance flatFppfDerivedQCoh_catCommSq_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] :
    CatCommSq (flatFppfInverseImageDerivedLQCohFbc X)
      (DerivedQCoh.quotientFunctor X)
      (𝟭 (DerivedQCohFlatFppf X))
      (flatFppfDerivedQCohInverseImage X) where
  iso := Functor.rightUnitor _ ≪≫
    (flatFppfDerivedQCohInverseImage_facIso X).symm

/-- Induced adjunction `Lg_! ⊣ g^*` between flat-fppf `D_QCoh` and
`D_QCoh(𝒪_X)`. -/
def flatFppfDerivedQCohLowerShriek.adjunction
    (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfDerivedQCohLowerShriek X ⊣
      flatFppfDerivedQCohInverseImage X :=
  (flatFppfLowerShriekDerivedQCoh.adjunction X).localization
    (𝟭 (DerivedQCohFlatFppf X))
    (MorphismProperty.isomorphisms (DerivedQCohFlatFppf X))
    (DerivedQCoh.quotientFunctor X)
    (derivedParasitic X).trW
    (flatFppfDerivedQCohLowerShriek X)
    (flatFppfDerivedQCohInverseImage X)

/-- The unit `id ⟶ Lg_! ⋙ g^*` is an isomorphism on flat-fppf `D_QCoh`. -/
instance flatFppfDerivedQCohLowerShriek_unit_app_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] (H : DerivedQCohFlatFppf X) :
    IsIso ((flatFppfDerivedQCohLowerShriek.adjunction X).unit.app H) :=
  sorry

/-- The counit `g^* ⋙ Lg_! ⟶ id` is an isomorphism on `D_QCoh(𝒪_X)`. -/
instance flatFppfDerivedQCohLowerShriek_counit_app_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] (E : DerivedQCoh X) :
    IsIso ((flatFppfDerivedQCohLowerShriek.adjunction X).counit.app E) :=
  sorry

/-- Composite of induced `g^*` with the `Lg_!` quasi-inverse is naturally
isomorphic to the identity on `D_QCoh(𝒪_X)`. -/
def flatFppfDerivedQCohInverseImage_comp_lowerShriek
    (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfDerivedQCohInverseImage X ⋙
        flatFppfDerivedQCohLowerShriek X ≅
      𝟭 (DerivedQCoh X) :=
  NatIso.ofComponents
    (fun E ↦ asIso
      ((flatFppfDerivedQCohLowerShriek.adjunction X).counit.app E))
    sorry

/-- Composite of the `Lg_!` quasi-inverse with induced `g^*` is naturally
isomorphic to the identity on flat-fppf `D_QCoh`. -/
def flatFppfDerivedQCohLowerShriek_comp_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfDerivedQCohLowerShriek X ⋙
        flatFppfDerivedQCohInverseImage X ≅
      𝟭 (DerivedQCohFlatFppf X) :=
  NatIso.ofComponents
    (fun H ↦
      (asIso
          ((flatFppfDerivedQCohLowerShriek.adjunction X).unit.app H)).symm)
    sorry

/-- The functors `g^*` and `Lg_!` are mutually inverse between `D_QCoh(𝒪_X)`
and flat-fppf `D_QCoh`. -/
instance flatFppfDerivedQCohInverseImage.instIsEquivalence
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfDerivedQCohInverseImage X).IsEquivalence :=
  Functor.IsEquivalence.mk'
    (flatFppfDerivedQCohLowerShriek X)
    (flatFppfDerivedQCohInverseImage_comp_lowerShriek X).symm
    (flatFppfDerivedQCohLowerShriek_comp_inverseImage X)

end AlgebraicGeometry.AlgebraicStack
