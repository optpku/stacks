/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.DerivedGlobalSections

/-!
# Derived global-sections comparisons for terminal hypercoverings

Typed checks of the Leray isomorphism and the canonical inverse-image comparison.
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

#check (CategoryTheory.SemiRepresentableFamily.rGammaDirectImageIso J K :
    directImageDerived J K ⋙
      RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v}) ≅
    RightDerived.Cochain.functor
      (Sheaf.Γ (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))

#check (CategoryTheory.SemiRepresentableFamily.rGammaInverseImageComparison J K :
    RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v}) ⟶
      inverseImageDerived J K ⋙
        RightDerived.Cochain.functor
          (Sheaf.Γ (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))

end CategoryTheory.SemiRepresentableFamily
