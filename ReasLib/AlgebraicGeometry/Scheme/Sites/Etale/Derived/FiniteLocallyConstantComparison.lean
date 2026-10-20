module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleModuleComparison
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.Closure

/-!
# Derived comparison of finite-type locally constant module sheaves

Derived inverse image from the small étale site to the small pro-étale site
restricts to an equivalence between the bounded-below derived full subcategories
whose cohomology sheaves are locally constant of finite type.
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

/-- For a scheme and a Noetherian coefficient ring, derived inverse image from
the small étale site to the small pro-étale site is an equivalence on the
bounded-below derived full subcategories whose cohomology sheaves are locally
constant sheaves of finite-type modules. -/
instance etaleToProEt_modulePlusPullback_locallyConstantFiniteType_isEquivalence :
    (etaleToProEt_modulePlusPullback_locallyConstantFiniteType X Λ).IsEquivalence :=
  sorry

end AlgebraicGeometry.Scheme

end

end
