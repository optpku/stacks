/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Triangulated
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.KProjective
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated

/-!
# Derived tensor functor associated to a complex

For a complex `K` of modules on a ringed site, this file derives the explicit DG functor
`- ⊗_(endDGA K) K` into the canonical Mathlib derived category of module sheaves.  It owns the
source functor, the total left-derived functor, its comparison transformation, and its shift and
triangulated structures.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.CochainComplex.Enriched
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace SheafOfModules.RingedSite.TensorWithObject.Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The homotopy-level tensor functor followed by the canonical ringed-site derived
localization. -/
@[stacks 09LX "homotopy-level derived tensor source functor"]
abbrev tensorSourceFunctor (K : Complex (J := J) (O := O)) :
    DifferentialGradedCategory.K ℤ (Modules K) ⥤
      RingedSiteDerived.max J O :=
  (TensorWithObject.tensorFunctor K).mapK ⋙
    @CochainComplex.Enriched.derivedQ _ _ _
      (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
        (J := J) (𝒪 := O))

/-- The standard-homotopy presentation of tensoring with `K`, followed by localization, agrees
with the enriched presentation used to define its total left-derived functor. -/
@[stacks 09LX "derived tensor source presentation"]
def tensorSourceIso (K : Complex (J := J) (O := O)) :
    TensorWithObject.homotopyFunctor K ⋙
        (@DerivedCategory.Qh _ _ _
          (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
            (J := J) (𝒪 := O)) :
          TensorWithObject.TargetHomotopy (J := J) (O := O) ⥤
            RingedSiteDerived.max J O) ≅
      tensorSourceFunctor K :=
  Functor.associator _ _ _

/-- The homotopy-level tensor functor followed by derived localization commutes with integer
shifts. -/
@[stacks 09LX "derived tensor source shift compatibility", reducible]
noncomputable def tensorSourceFunctor_commShift
    (K : Complex (J := J) (O := O)) : (tensorSourceFunctor K).CommShift ℤ :=
  @Functor.CommShift.ofIso _ _ _ _ _ _ (tensorSourceIso K) ℤ _ _ _
    (@Functor.CommShift.comp _ _ _ _ _ _
      (TensorWithObject.homotopyFunctor K)
      (@DerivedCategory.Qh _ _ _
        (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
          (J := J) (𝒪 := O)))
      _ _ _ _ _ (TensorWithObject.homotopyFunctor_commShift K) _)

/-- Source-level definedness of the total left derived tensor functor. -/
@[stacks 09LX "everywhere-defined derived tensor source"]
abbrev HasTensorFunctor (K : Complex (J := J) (O := O)) : Prop :=
  Functor.LeftDerived.EverywhereDefined (tensorSourceFunctor K)
    (DifferentialGradedModule.quasiIso (endDGA K))

/-- Property-(P) resolutions define tensoring with `K` at every object of the DG-module
derived category. -/
theorem hasTensorFunctor (K : Complex (J := J) (O := O)) :
    HasTensorFunctor K := sorry

/-- The total left-derived functor `- ⊗^L_(endDGA K) K` from DG modules to the
ringed-site derived category. -/
@[stacks 09LX "derived tensor with a complex over its endomorphism DGA"]
noncomputable def tensorFunctor (K : Complex (J := J) (O := O)) :
    DifferentialGradedModule.Derived.Category (endDGA K) ⥤
      RingedSiteDerived.max J O :=
  @Functor.totalLeftDerived _ _ _ _ _ _
    (tensorSourceFunctor K)
    (DifferentialGradedModule.Derived.Q (endDGA K))
    (DifferentialGradedModule.quasiIso (endDGA K)) _
    (@Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _ _ _
      (tensorSourceFunctor K) (DifferentialGradedModule.quasiIso (endDGA K))
      (@Functor.LeftDerived.EverywhereDefined.hasPointwise _ _ _ _ _ _
        (hasTensorFunctor K)))

/-- The canonical comparison from derived tensoring to homotopy-level tensoring. -/
@[stacks 09LX "derived tensor comparison transformation"]
noncomputable def tensorCounit (K : Complex (J := J) (O := O)) :
    DifferentialGradedModule.Derived.Q (endDGA K) ⋙ tensorFunctor K ⟶
      tensorSourceFunctor K :=
  @Functor.totalLeftDerivedCounit _ _ _ _ _ _
    (tensorSourceFunctor K)
    (DifferentialGradedModule.Derived.Q (endDGA K))
    (DifferentialGradedModule.quasiIso (endDGA K)) _
    (@Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _ _ _
      (tensorSourceFunctor K) (DifferentialGradedModule.quasiIso (endDGA K))
      (@Functor.LeftDerived.EverywhereDefined.hasPointwise _ _ _ _ _ _
        (hasTensorFunctor K)))

/-- Property-(P) objects compute the total left-derived tensor functor without replacing the
source module. -/
@[stacks 09LX "property-P objects compute derived tensor"]
theorem tensorComputesAt (K : Complex (J := J) (O := O))
    (M : Modules K) (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    Functor.LeftDerived.ComputesAt (tensorSourceFunctor K)
      (DifferentialGradedModule.quasiIso (endDGA K))
      ((DifferentialGradedModule.toK (endDGA K)).obj M) := sorry

/-- For a property-(P) module, the canonical derived-to-underived tensor comparison is an
isomorphism. -/
@[stacks 09LX "property-P derived tensor comparison is an isomorphism"]
theorem tensorCounitApp_isIso (K : Complex (J := J) (O := O))
    (M : Modules K) (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    IsIso ((tensorCounit K).app
      ((DifferentialGradedModule.toK (endDGA K)).obj M)) := sorry

/-- The canonical comparison identifying derived tensor with its strict value on a
property-(P) module. -/
@[stacks 09LX "property-P derived tensor comparison isomorphism"]
noncomputable def tensorCounitAppIso (K : Complex (J := J) (O := O))
    (M : Modules K) (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorFunctor K).obj
        ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj M) ≅
      (tensorSourceFunctor K).obj
        ((DifferentialGradedModule.toK (endDGA K)).obj M) :=
  @asIso _ _ _ _
    ((tensorCounit K).app
      ((DifferentialGradedModule.toK (endDGA K)).obj M))
    (tensorCounitApp_isIso K M hM)

/-- The forward map of `tensorCounitAppIso` is the derived tensor counit component. -/
@[simp, stacks 09LX "forward property-P derived tensor comparison"]
theorem tensorCounitAppIso_hom (K : Complex (J := J) (O := O))
    (M : Modules K) (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorCounitAppIso K M hM).hom =
      (tensorCounit K).app
        ((DifferentialGradedModule.toK (endDGA K)).obj M) := sorry

/-- The inverse map of `tensorCounitAppIso` is the inverse of its counit component. -/
@[simp, stacks 09LX "inverse property-P derived tensor comparison"]
theorem tensorCounitAppIso_inv (K : Complex (J := J) (O := O))
    (M : Modules K) (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorCounitAppIso K M hM).inv =
      (@asIso _ _ _ _
        ((tensorCounit K).app
          ((DifferentialGradedModule.toK (endDGA K)).obj M))
        (tensorCounitApp_isIso K M hM)).inv := sorry

/-- On a property-(P) module, derived tensor is canonically represented by the ordinary tensor
complex in the standard Mathlib derived category. -/
@[stacks 09LX "property-P ordinary model of derived tensor"]
noncomputable def tensorModelIso (K : Complex (J := J) (O := O))
    (M : Modules K) (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorFunctor K).obj
        ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj M) ≅
      (@DerivedCategory.Q _ _ _
        (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
          (J := J) (𝒪 := O))).obj ((TensorWithObject.tensorFunctor K).obj M) :=
  tensorCounitAppIso K M hM ≪≫
    @CochainComplex.Enriched.derivedQObjIso _ _ _
      (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
        (J := J) (𝒪 := O))
      ((TensorWithObject.tensorFunctor K).obj M)

/-- The forward strict-model map is the counit comparison followed by derived localization. -/
@[simp, stacks 09LX "forward property-P derived tensor model comparison"]
theorem tensorModelIso_hom (K : Complex (J := J) (O := O))
    (M : Modules K) (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorModelIso K M hM).hom =
      (tensorCounitAppIso K M hM).hom ≫
        (@CochainComplex.Enriched.derivedQObjIso _ _ _
          (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
            (J := J) (𝒪 := O))
          ((TensorWithObject.tensorFunctor K).obj M)).hom := sorry

/-- The inverse strict-model map reverses localization and the counit comparison. -/
@[simp, stacks 09LX "inverse property-P derived tensor model comparison"]
theorem tensorModelIso_inv (K : Complex (J := J) (O := O))
    (M : Modules K) (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorModelIso K M hM).inv =
      (@CochainComplex.Enriched.derivedQObjIso _ _ _
        (SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
          (J := J) (𝒪 := O))
          ((TensorWithObject.tensorFunctor K).obj M)).inv ≫
        (tensorCounitAppIso K M hM).inv := sorry

/-- The concrete derived tensor functor, together with `tensorCounit`, is a left-derived
functor model. -/
@[stacks 09LX "derived tensor universal property"]
theorem tensorFunctor_isLeftDerived (K : Complex (J := J) (O := O)) :
    (tensorFunctor K).IsLeftDerivedFunctor (tensorCounit K)
      (DifferentialGradedModule.quasiIso (endDGA K)) := sorry

/-- Derived tensoring with `K` commutes with integer shifts. -/
@[stacks 09LX "derived tensor commutes with shifts", reducible]
noncomputable def tensorFunctor_commShift
    (K : Complex (J := J) (O := O)) : (tensorFunctor K).CommShift ℤ :=
  @Functor.totalLeftDerived_commShift _ _ _ _ _ _ (tensorSourceFunctor K)
    (DifferentialGradedModule.quasiIso (endDGA K))
    (DifferentialGradedModule.Derived.Q (endDGA K)) _ _ _
    (tensorSourceFunctor_commShift K) _ _
    (@Functor.LeftDerived.EverywhereDefined.hasPointwise _ _ _ _ _ _
      (hasTensorFunctor K))

/-- Derived tensoring with `K` is triangulated. -/
@[stacks 09LX "derived tensor is triangulated"]
theorem tensorFunctor_isTriangulated (K : Complex (J := J) (O := O)) :
    (tensorFunctor K).IsTriangulatedWith (tensorFunctor_commShift K) := sorry

end SheafOfModules.RingedSite.TensorWithObject.Derived
