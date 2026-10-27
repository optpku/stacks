/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.DerivedDescent

/-!
# Derived adjunction of a hypercovering

Typed checks of the exact inverse image, derived functors, adjunctions, and units
for a hypercovering of the terminal presheaf.
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

#check (CategoryTheory.SemiRepresentableFamily.inverseImageExact J K :
    Sheaf J AddCommGrpCat.{max w u v} ⥤ₑ
      Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.inverseImageDerived J K :
    DerivedCategory (Sheaf J AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))

#check (CategoryTheory.SemiRepresentableFamily.directImage_additive J K :
    (directImage J K.simplicial AddCommGrpCat.{max w u v}).Additive)

#check (CategoryTheory.SemiRepresentableFamily.directImageDerived J K :
    DerivedCategory
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory (Sheaf J AddCommGrpCat.{max w u v}))

#check (CategoryTheory.SemiRepresentableFamily.derivedAdjunction J K :
    inverseImageDerived J K ⊣ directImageDerived J K)

#check (CategoryTheory.SemiRepresentableFamily.derivedUnit J K :
    𝟭 (DerivedCategory (Sheaf J AddCommGrpCat.{max w u v})) ⟶
      inverseImageDerived J K ⋙ directImageDerived J K)

section Plus

variable [(directImage J K.simplicial AddCommGrpCat.{max w u v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))]

#check (CategoryTheory.SemiRepresentableFamily.plusInverseImageDerived J K :
    DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))

#check (CategoryTheory.SemiRepresentableFamily.plusDirectImageDerived J K :
    DerivedCategory.Plus
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}))

#check (CategoryTheory.SemiRepresentableFamily.plusDerivedAdjunction J K :
    plusInverseImageDerived J K ⊣ plusDirectImageDerived J K)

#check (CategoryTheory.SemiRepresentableFamily.plusDerivedUnit J K :
    𝟭 (DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) ⟶
      plusInverseImageDerived J K ⋙ plusDirectImageDerived J K)

#check (CategoryTheory.SemiRepresentableFamily.plusDerivedUnit_app_isIso J K :
  ∀ E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}),
    IsIso ((plusDerivedUnit J K).app E))

end Plus

end CategoryTheory.SemiRepresentableFamily
