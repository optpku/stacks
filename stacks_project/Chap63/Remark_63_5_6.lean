module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace
public import stacks_project.Chap59.Proposition_59_70_3
public import stacks_project.Chap63.Example_63_5_5_Trace_for_flat_quasi_finite_Trace
public import stacks_project.Chap63.Lemma_63_4_3
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

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [LocallyQuasiFinite j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback j).op.HasLeftKanExtension P]

/-- Remark 63.5.6 (1): Let `j : U ⟶ X` be an étale morphism of schemes. Then
the trace map `Tr : j_! j⁻¹ K ⟶ K` of Example 63.5.5 equals the counit of
the adjunction `j_! ⊣ j⁻¹`, after the identification
`extensionByZeroIsoLowerShriek` of Lemma 63.4.3. -/
@[stacks 0GL4]
theorem fiberWeightTraceHom_eq_abelianEtaleTrace
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (extensionByZeroIsoLowerShriek j).inv.app
        ((etaleAbelianSheafPullback j).obj F) ≫
      (abelianExtensionByZero j).map
        ((etaleRestrictionSheafIso_smallEtalePullback j F).inv) ≫
      (abelianEtaleTrace j).app F =
      fiberWeightTraceHom j F :=
  sorry

/- Remark 63.5.6 (2): Section 59.66 already used the terminology "trace" for
this counit of `j_! ⊣ j⁻¹` on abelian étale sheaves. -/
@[stacks 0GL4] #check
  (abelianEtaleTrace j :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ abelianExtensionByZero j ⟶
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))

end AlgebraicGeometry.Scheme.Etale

end
