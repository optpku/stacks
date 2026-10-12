/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.ToExterior
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.SecondOrder
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.CohomologyProduct
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open RingedSpace
open SheafOfModules.RingedSite
open DerivedCategory MonoidalClosed ModuleDerived ExteriorPower
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSubobject

/-- The quotient structure module `𝒪_Y / I`, placed in degree zero of `D(𝒪_Y)`. -/
noncomputable def idealQuotientDerived {Y : RingedSpace.{u}}
    (I : IdealSubobject Y) : ModuleDerived Y :=
  (singleFunctor Y.Modules 0).obj (quotientStructureModule I)

/-- `idealQuotientDerived I` is the degree-zero derived object attached to `𝒪_Y / I`. -/
theorem idealQuotientDerived_def {Y : RingedSpace.{u}} (I : IdealSubobject Y) :
    idealQuotientDerived I =
      (singleFunctor Y.Modules 0).obj (quotientStructureModule I) := sorry

/-- The selected derived endomorphism object `RHom(𝒪_Y / I, 𝒪_Y / I)`. -/
noncomputable def derivedQuotientEndomorphism
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) : ModuleDerived Y :=
  (ihomOf H (idealQuotientDerived I)).obj (idealQuotientDerived I)

/-- `derivedQuotientEndomorphism H I` is the internal Hom selected by `H`. -/
theorem derivedQuotientEndomorphism_def
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) :
    derivedQuotientEndomorphism H I =
      (ihomOf H (idealQuotientDerived I)).obj (idealQuotientDerived I) := sorry

/-- The sheaf `Extⁱ(𝒪_Y / I, 𝒪_Y / I)` computed from the selected derived internal Hom. -/
noncomputable def quotientSelfExt
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) (i : ℤ) : Y.Modules :=
  cohomologySheaf (derivedQuotientEndomorphism H I) i

/-- `quotientSelfExt H I i` is the `i`-th cohomology sheaf of the selected derived
endomorphism object. -/
theorem quotientSelfExt_def
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) (i : ℤ) :
    quotientSelfExt H I i = cohomologySheaf (derivedQuotientEndomorphism H I) i := sorry

/-- The canonical product on the self-`Ext` sheaves of `𝒪_Y / I`, obtained from the K-flat
cohomology product followed by composition in the selected derived internal Hom. -/
noncomputable def quotientSelfExtProduct
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) (p q : ℤ) :
    (quotientSelfExt H I p : Y.Modules) ⊗ (quotientSelfExt H I q : Y.Modules) ⟶
      quotientSelfExt H I (p + q) :=
  ModuleDerived.derivedSheafCohomologyProduct (derivedQuotientEndomorphism H I)
      (derivedQuotientEndomorphism H I) p q ≫
    cohomologySheafMap
      (MonoidalClosed.compOf H (idealQuotientDerived I)
        (idealQuotientDerived I) (idealQuotientDerived I)) (p + q)

/-- The self-`Ext` product is the K-flat cohomology product followed by derived internal-Hom
composition. -/
theorem quotientSelfExtProduct_def
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) (p q : ℤ) :
    quotientSelfExtProduct H I p q =
      ModuleDerived.derivedSheafCohomologyProduct (derivedQuotientEndomorphism H I)
          (derivedQuotientEndomorphism H I) p q ≫
        cohomologySheafMap
          (MonoidalClosed.compOf H (idealQuotientDerived I)
            (idealQuotientDerived I) (idealQuotientDerived I)) (p + q) := sorry

/-- The unit of the canonical composition algebra on the self-`Ext` sheaves of `𝒪_Y / I`. -/
noncomputable def quotientSelfExtUnit
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) :
    TensorPower.sheaf Y.sheaf (quotientSelfExt H I 1) 0 ⟶ quotientSelfExt H I 0 :=
  RingedSpace.unitModuleToTensorUnit Y ≫
    (ModuleDerived.derivedTensorUnitCohomologyIso Y).inv ≫
      cohomologySheafMap (MonoidalClosed.id (idealQuotientDerived I)) 0

/-- The self-`Ext` unit is induced by the identity of `𝒪_Y / I`. -/
theorem quotientSelfExtUnit_def
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) :
    quotientSelfExtUnit H I =
      RingedSpace.unitModuleToTensorUnit Y ≫
        (ModuleDerived.derivedTensorUnitCohomologyIso Y).inv ≫
          cohomologySheafMap (MonoidalClosed.id (idealQuotientDerived I)) 0 := sorry

/-- The canonical iterated product on `Ext¹(𝒪_Y / I, 𝒪_Y / I)`, formed from the K-flat
cohomology product and composition on the selected derived internal Hom. -/
noncomputable def compositionTensorPowerMap
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) :
    (i : ℕ) → TensorPower.sheaf Y.sheaf (quotientSelfExt H I 1) i ⟶
      quotientSelfExt H I i
  | 0 => quotientSelfExtUnit H I
  | i + 1 =>
      (𝟙 (quotientSelfExt H I 1) ⊗ₘ compositionTensorPowerMap H I i) ≫
        (β_ (quotientSelfExt H I 1) (quotientSelfExt H I i)).hom ≫
          quotientSelfExtProduct H I i 1

/-- The canonical iterated composition product starts with the identity class in degree zero. -/
theorem compositionTensorPowerMap_zero
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) :
    compositionTensorPowerMap H I 0 = quotientSelfExtUnit H I := sorry

/-- Successive canonical tensor-power products are obtained from the preceding product and
composition on self-`Ext`. -/
theorem compositionTensorPowerMap_succ
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) (i : ℕ) :
    compositionTensorPowerMap H I (i + 1) =
      (𝟙 (quotientSelfExt H I 1) ⊗ₘ compositionTensorPowerMap H I i) ≫
        (β_ (quotientSelfExt H I 1) (quotientSelfExt H I i)).hom ≫
          quotientSelfExtProduct H I i 1 := sorry

/-- The canonical iterated composition product is constant on the relations defining the
exterior power. -/
theorem compositionTensorPowerMap_respectsExterior
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
    [IsKoszulRegularIdealSheaf I] (i : ℕ) :
    ∀ {Z : Y.Modules}
      (g₁ g₂ : Z ⟶ TensorPower.sheaf Y.sheaf (quotientSelfExt H I 1) i),
      g₁ ≫ TensorPower.toExterior Y.sheaf (quotientSelfExt H I 1) i =
          g₂ ≫ TensorPower.toExterior Y.sheaf (quotientSelfExt H I 1) i →
        g₁ ≫ compositionTensorPowerMap H I i =
          g₂ ≫ compositionTensorPowerMap H I i := sorry

/-- The canonical morphism from the exterior power of `Ext¹` to `Extⁱ`, obtained by descending
the iterated cohomology product induced by internal-Hom composition. -/
noncomputable def compositionExteriorPowerMap
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
    [IsKoszulRegularIdealSheaf I] (i : ℕ) :
    ExteriorPower.sheaf (quotientSelfExt H I 1) i ⟶ quotientSelfExt H I i :=
  @EffectiveEpi.desc _ _ _ _ _
    (TensorPower.toExterior Y.sheaf (quotientSelfExt H I 1) i)
    (RegularEpi.effectiveEpi (regularEpiOfEpi
      (TensorPower.toExterior Y.sheaf (quotientSelfExt H I 1) i)))
    (compositionTensorPowerMap H I i)
    (compositionTensorPowerMap_respectsExterior H I i)

/-- The composition-induced exterior-power map factors the iterated product through the canonical
tensor-to-exterior projection. -/
theorem compositionExteriorPowerMap_factorization
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
    [IsKoszulRegularIdealSheaf I] (i : ℕ) :
    TensorPower.toExterior Y.sheaf (quotientSelfExt H I 1) i ≫
        compositionExteriorPowerMap H I i = compositionTensorPowerMap H I i := sorry

/-- If `I ⊆ 𝒪_Y` is Koszul-regular and `Q = 𝒪_Y / I`, then composition on `RHom(Q, Q)`
induces an isomorphism from the `i`-th exterior power of `Ext¹(Q, Q)` to `Extⁱ(Q, Q)`
for every `i : ℕ`. -/
noncomputable instance compositionExteriorPowerMap_isIso
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
    [IsKoszulRegularIdealSheaf I] (i : ℕ) :
    IsIso (compositionExteriorPowerMap H I i) := sorry

end AlgebraicGeometry.RingedSpace.IdealSubobject
