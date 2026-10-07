module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap61.Lemma_61_19_8_Comparison

/-!
# Restricted derived inverse image on finite-type locally constant cohomology

Derived inverse image `ε⁻¹` along `etaleToProEt` preserves bounded-below complexes
whose cohomology sheaves are locally constant of finite type, and therefore
restricts to a functor between the corresponding full subcategories of
`D⁺(X.Etale, Λ)` and `D⁺(X.ProEt, Λ)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [PreservesFiniteLimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))]
variable [PreservesFiniteColimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))]
variable [∀ U : X.Etale,
    HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.ProEt,
    HasWeakSheafify ((ProEt.topology X).over U) (ModuleCat.{u + 1} Λ)]

/-- Inverse image along `etaleToProEt` preserves locally constant sheaves of
finite-type `Λ`-modules. -/
instance etaleToProEtPullback_isFiniteTypeLocallyConstantModule
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteTypeLocallyConstantModule F] :
    IsFiniteTypeLocallyConstantModule
      ((etaleToProEtPullback X (ModuleCat.{u + 1} Λ)).obj F) :=
  sorry

/-- Bounded-below derived objects whose cohomology sheaves are locally constant
of finite type are sent by derived `ε⁻¹` into the corresponding pro-étale class. -/
theorem etaleToProEt_modulePlusPullback_locallyConstantFiniteType_le :
    DerivedCategory.Plus.cohomologyIn
        (finiteTypeLocallyConstantModule X.smallEtaleTopology Λ) ≤
      ObjectProperty.inverseImage
        (DerivedCategory.Plus.cohomologyIn
          (finiteTypeLocallyConstantModule (ProEt.topology X) Λ))
        (etaleToProEt_modulePlusPullback X Λ) :=
  sorry

/-- Inverse image `ε⁻¹` along `etaleToProEt`, restricted to `D⁺` objects whose
cohomology sheaves are locally constant sheaves of finite-type `Λ`-modules. -/
def etaleToProEt_modulePlusPullback_locallyConstantFiniteType :
    DerivedCategory.Plus.CohomologyIn
      (finiteTypeLocallyConstantModule X.smallEtaleTopology Λ) ⥤
      DerivedCategory.Plus.CohomologyIn
        (finiteTypeLocallyConstantModule (ProEt.topology X) Λ) :=
  ObjectProperty.FullSubcategory.restrict
    (etaleToProEt_modulePlusPullback X Λ)
    (etaleToProEt_modulePlusPullback_locallyConstantFiniteType_le X Λ)

end AlgebraicGeometry.Scheme

end

end
