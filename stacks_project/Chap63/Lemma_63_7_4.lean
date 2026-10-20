module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ClosedOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u v

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (Λ : Type v) [CommRing Λ]
variable [∀ F : (closedImmersionComplement i).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
    (etaleRestriction (closedImmersionComplement i).ι).op.HasLeftKanExtension F]
variable [∀ G : X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
    (smallEtalePullback i).op.HasLeftKanExtension G]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasWeakSheafify (closedImmersionComplement i).toScheme.smallEtaleTopology
    (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf Z.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology
    (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
    (etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
    (etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
    (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
    (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{v} Λ))]
variable [((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
    X.smallEtaleTopology Z.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
    ((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology)]
variable [PreservesFiniteColimits
    ((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology)]
variable [((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
    X.smallEtaleTopology Z.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
    ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology)]
variable [PreservesFiniteColimits
    ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology)]
variable [(moduleClosedOpenLower i Λ).Additive]
variable [(moduleClosedOpenClosed i Λ).Additive]
variable [PreservesFiniteLimits (moduleClosedOpenLower i Λ)]
variable [PreservesFiniteColimits (moduleClosedOpenLower i Λ)]
variable [PreservesFiniteLimits (moduleClosedOpenClosed i Λ)]
variable [PreservesFiniteColimits (moduleClosedOpenClosed i Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory
    (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale,
    HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ U : Z.Etale,
    HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ U : (closedImmersionComplement i).toScheme.Etale,
    HasWeakSheafify
      ((closedImmersionComplement i).toScheme.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]

namespace AlgebraicGeometry.Scheme.Etale

variable (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))

/- Lemma 63.7.4 -/
@[stacks 0GKL] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedClosedOpenTriangle_distinguished
    (i := i) (Λ := Λ) K :
      etaleDerivedClosedOpenTriangle i Λ K ∈
        distTriang (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))))

end AlgebraicGeometry.Scheme.Etale
