/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.DerivedGlobalSections

/-!
# Lemma 85.17.4

Let `C` be a site with equalizers and fibre products, and let `K` be a
hypercovering. For every `E` in `D(C)` there is a canonical isomorphism
`RΓ(C, E) ≅ RΓ((C / K)_total, a⁻¹ E)` in `D(Ab)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [h_eq : HasEqualizers C] [h_pb : HasPullbacks C]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasSheafify J AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{max w u v}]
variable [HasGlobalSectionsFunctor (overSiteTotalTopology J K.simplicial)
    AddCommGrpCat.{max w u v}]
variable [(RightDerived.Cochain.toDerived
    (Sheaf.Γ J AddCommGrpCat.{max w u v})).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf J AddCommGrpCat.{max w u v}) (up ℤ))]
variable [(RightDerived.Cochain.toDerived
    (Sheaf.Γ (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v})).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) (up ℤ))]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/- Lemma 85.17.4: For a site with equalizers and fibre products and a hypercovering,
the canonical comparison `RΓ(C, E) ⟶ RΓ((C / K)_total, a⁻¹ E)` is an isomorphism
for every `E` in the unbounded derived category of abelian sheaves. -/
@[stacks 0D8H] #check (CategoryTheory.SemiRepresentableFamily.rGammaInverseImageComparison_app_isIso J K :
  ∀ E : DerivedCategory (Sheaf J AddCommGrpCat.{max w u v}),
    IsIso ((rGammaInverseImageComparison J K).app E))

end CategoryTheory.SemiRepresentableFamily
