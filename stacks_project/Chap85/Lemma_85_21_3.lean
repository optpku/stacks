/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import stacks_project.Chap85.Lemma_85_19_3

/-!
# Lemma 85.21.3

Let `C` be a site with fibre products and `X` an object of `C`. Let
`a : U ⟶ X` be a hypercovering of `X` in `C`. Then there is a canonical
isomorphism `RΓ(X, E) ≅ RΓ((C / U)_total, a⁻¹ E)` in `D(Ab)` for every
`E` in `D(C / X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]
variable [h_pb : HasPullbacks C]
include h_pb
variable (J : GrothendieckTopology C) (A : SimplicialObject.Augmented C)
variable (hA : A.IsHypercovering J)
variable [HasSheafify (J.over A.right) AddCommGrpCat.{max w u v}]
variable [HasSheafify
    (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [HasGlobalSectionsFunctor (J.over A.right) AddCommGrpCat.{max w u v}]
variable [HasGlobalSectionsFunctor
    (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [(RightDerived.Cochain.toDerived
    (Sheaf.Γ (J.over A.right) AddCommGrpCat.{max w u v})).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (J.over A.right) AddCommGrpCat.{max w u v})
      (up ℤ))]
variable [(RightDerived.Cochain.toDerived
    (Sheaf.Γ (overSiteTotalTopology (J.over A.right)
        (toHypercovering.{w} A hA).toSimplicialObject)
      AddCommGrpCat.{max w u v})).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso
      (Sheaf (overSiteTotalTopology (J.over A.right)
          (toHypercovering.{w} A hA).toSimplicialObject)
        AddCommGrpCat.{max w u v})
      (up ℤ))]
variable [∀ P : (Grothendieck
      (overSiteDiagram (toHypercovering.{w} A hA).toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget (toHypercovering.{w} A hA).toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.21.3: Let `C` be a site with fibre products and `X` an object of
`C`. Let `a : U ⟶ X` be a hypercovering of `X` in `C` as defined above. For
`E ∈ D(C / X)` the canonical map `RΓ(X, E) ⟶ RΓ((C / U)_total, a⁻¹ E)` is an
isomorphism. -/
@[stacks 09X9]
theorem rGammaInverseImageComparison_app_isIso
    (E : DerivedCategory (Sheaf (J.over A.right) AddCommGrpCat.{max w u v})) :
    IsIso ((Hypercovering.rGammaInverseImageComparison J A.right (toHypercovering.{w} A hA)).app E) :=
  sorry

/-- The comparison `RΓ(X, -) ⟶ a⁻¹ ⋙ RΓ((C / U)_total, -)` is an isomorphism of
functors on `D(C / X)`. -/
theorem rGammaInverseImageComparison_isIso :
    IsIso (Hypercovering.rGammaInverseImageComparison J A.right (toHypercovering.{w} A hA)) :=
  sorry

end CategoryTheory.SimplicialObject.Augmented
