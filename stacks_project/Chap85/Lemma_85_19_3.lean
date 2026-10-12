/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_19_3_Comparison

/-!
# Lemma 85.19.3

Let `C` be a site with fibre products and `X` an object of `C`. Let `K` be a
hypercovering of `X`. Then there is a canonical isomorphism
`RΓ(X, E) ≅ RΓ((C / K)_total, a⁻¹ E)` in `D(Ab)` for every `E` in `D(C / X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [h_pb : HasPullbacks C]
include h_pb
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)
variable [HasSheafify (J.over X) AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [HasGlobalSectionsFunctor (J.over X) AddCommGrpCat.{max w u v}]
variable [HasGlobalSectionsFunctor
    (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [(RightDerived.Cochain.toDerived
    (Sheaf.Γ (J.over X) AddCommGrpCat.{max w u v})).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (J.over X) AddCommGrpCat.{max w u v})
      (up ℤ))]
variable [(RightDerived.Cochain.toDerived
    (Sheaf.Γ (overSiteTotalTopology (J.over X) K.toSimplicialObject)
      AddCommGrpCat.{max w u v})).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso
      (Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
        AddCommGrpCat.{max w u v})
      (up ℤ))]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.19.3: Let `C` be a site with fibre products and `X` an object of
`C`. Let `K` be a hypercovering of `X`. For `E ∈ D(C / X)` the canonical map
`RΓ(X, E) ⟶ RΓ((C / K)_total, a⁻¹ E)` is an isomorphism. -/
@[stacks 09X7]
theorem rGammaInverseImageComparison_app_isIso
    (E : DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max w u v})) :
    IsIso ((rGammaInverseImageComparison J X K).app E) :=
  sorry

/-- The comparison `RΓ(X, -) ⟶ a⁻¹ ⋙ RΓ((C / K)_total, -)` is an isomorphism of
functors. -/
theorem rGammaInverseImageComparison_isIso :
    IsIso (rGammaInverseImageComparison J X K) :=
  sorry

end CategoryTheory.Hypercovering
