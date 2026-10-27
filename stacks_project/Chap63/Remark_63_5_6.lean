/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Etale
import StacksCheckRecall

/-!
# Étale fibre-weight traces are adjunction counits

Remark 63.5.6: for an étale morphism `j : U ⟶ X`, the fibre-weight trace of
Example 63.5.5 coincides with the counit of `j_! ⊣ j⁻¹`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback j).op.HasLeftKanExtension P]

variable (Λ : Type u) [CommRing Λ]
variable [U.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback j).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]
variable [∀ V : U.Etale,
  HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ V : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]

/- Remark 63.5.6: For an étale morphism `j : U ⟶ X`, the trace of
Example 63.5.5 on derived étale `Λ`-module sheaves equals the counit of
`j_! ⊣ j⁻¹`. Section 59.66 already used the terminology "trace" for this counit. -/
@[stacks 0GL4] #check
  (AlgebraicGeometry.Scheme.Etale.fiberWeightTraceDerivedHom_eq_counit j Λ :
    ∀ K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)),
      fiberWeightTraceDerivedHom j Λ K =
        (lowerShriekModuleDerivedEtaleAdjunction j Λ).counit.app K)

end AlgebraicGeometry.Scheme.Etale

end
