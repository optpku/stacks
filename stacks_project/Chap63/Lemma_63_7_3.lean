/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.MayerVietoris
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

/-!
# Mayer–Vietoris distinguished triangle for étale derived extension by zero
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale


variable {X : Scheme.{u}} (U V : X.Opens)
variable (Λ : Type v) [CommRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : U.toScheme.Etale,
  HasWeakSheafify (U.toScheme.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify V.toScheme.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : V.toScheme.Etale,
  HasWeakSheafify (V.toScheme.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : (U ⊓ V).toScheme.Etale,
  HasWeakSheafify ((U ⊓ V).toScheme.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory
  (Sheaf (U ⊓ V).toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ F : U.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction (U.ι)).op.HasLeftKanExtension F]
variable [∀ F : V.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction (V.ι)).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction ((U ⊓ V).ι)).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)))).op.HasLeftKanExtension F]
variable [∀ F : (U ⊓ V).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction ((X.homOfLE (inf_le_right : U ⊓ V ≤ V)))).op.HasLeftKanExtension F]
variable [(etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf ((U ⊓ V).ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf ((U ⊓ V).ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf ((U ⊓ V).ι) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)))
    (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U))) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U))) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V)))
    (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V))) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V))) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero ((U ⊓ V).ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero ((U ⊓ V).ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero ((U ⊓ V).ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_left : U ⊓ V ≤ U)))
      (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]

/- Lemma 63.7.3 -/
@[stacks 0GKK] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerived_mayerVietoris_lowerShriek_triangle U V Λ :
    U ⊔ V = ⊤ →
      ∃ δ : 𝟭 (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) ⟶
        etaleDerivedExtensionByZeroRestrict ((U ⊓ V).ι) Λ ⋙
          shiftFunctor (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (1 : ℤ),
      ∀ K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)),
        Triangle.mk
            ((mayerVietorisLowerShriekToBiprod U V Λ).app K)
            ((mayerVietorisLowerShriekFromBiprod U V Λ).app K)
            (δ.app K) ∈ distTriang (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))))

end AlgebraicGeometry.Scheme.Etale

end
