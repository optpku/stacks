/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.DerivedAdjunction

/-!
# Derived descent for terminal hypercoverings
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
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
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/-- The canonical derived unit of a terminal hypercovering is invertible on every object
of the unbounded derived category of abelian sheaves. -/
instance derivedUnit_app_isIso
    (E : DerivedCategory (Sheaf J AddCommGrpCat.{max w u v})) :
    IsIso ((derivedUnit J K).app E) := sorry

/-- The derived adjunction unit of a terminal hypercovering is an isomorphism of functors
on the unbounded derived category of abelian sheaves. -/
instance derivedUnit_isIso : IsIso (derivedUnit J K) := sorry

section Plus

variable [(directImage J K.simplicial AddCommGrpCat.{max w u v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))]

/-- The canonical derived unit of a terminal hypercovering is invertible on every object
of the bounded-below derived category of abelian sheaves. -/
instance plusDerivedUnit_app_isIso
    (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) :
    IsIso ((plusDerivedUnit J K).app E) := sorry

end Plus

end CategoryTheory.SemiRepresentableFamily
