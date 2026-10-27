/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.SheafDescent

/-!
# Derived adjunctions for terminal hypercoverings

The exact inverse image and additive direct image of a terminal hypercovering induce
adjunctions on unbounded and bounded-below derived categories of abelian sheaves.
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

/-- The exact inverse-image functor `a⁻¹` on abelian sheaves along `j_total`. -/
abbrev inverseImageExact :
    Sheaf J AddCommGrpCat.{max w u v} ⥤ₑ
      Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v} :=
  siteAbelianInverseImageExact (overSiteTotalTopology J K.simplicial) J
    (totalForget K.simplicial)

/-- Unbounded derived inverse image `a⁻¹` on `D(C)`. -/
abbrev inverseImageDerived :
    DerivedCategory (Sheaf J AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) :=
  Adjunction.Derived.KInjective.left (inverseImageExact J K)

/-- Direct image `a_*` of abelian sheaves along `j_total` is additive. -/
instance directImage_additive :
    (directImage J K.simplicial AddCommGrpCat.{max w u v}).Additive :=
  (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v}).right_adjoint_additive

/-- Unbounded total right-derived direct image `Ra_*` along `j_total`. -/
abbrev directImageDerived :
    DerivedCategory
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory (Sheaf J AddCommGrpCat.{max w u v}) :=
  Adjunction.Derived.KInjective.right
    (directImage J K.simplicial AddCommGrpCat.{max w u v})

/-- The unbounded derived adjunction `a⁻¹ ⊣ Ra_*` attached to a hypercovering. -/
def derivedAdjunction :
    inverseImageDerived J K ⊣ directImageDerived J K :=
  Adjunction.Derived.KInjective.adjunction (inverseImageExact J K)
    (directImage J K.simplicial AddCommGrpCat.{max w u v})
    (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v})

/-- The canonical derived unit `E ⟶ Ra_* a⁻¹ E`. -/
abbrev derivedUnit :
    𝟭 (DerivedCategory (Sheaf J AddCommGrpCat.{max w u v})) ⟶
      inverseImageDerived J K ⋙ directImageDerived J K :=
  (derivedAdjunction J K).unit

section Plus

variable [(directImage J K.simplicial AddCommGrpCat.{max w u v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))]

/-- Bounded-below derived inverse image `a⁻¹` on `D⁺(C)`. -/
abbrev plusInverseImageDerived :
    DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) :=
  Adjunction.Derived.Plus.left (inverseImageExact J K)

/-- Bounded-below total right-derived direct image `Ra_*` on `D⁺`. -/
abbrev plusDirectImageDerived :
    DerivedCategory.Plus
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) ⥤
      DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v}) :=
  Adjunction.Derived.Plus.right
    (directImage J K.simplicial AddCommGrpCat.{max w u v})

/-- The bounded-below derived adjunction `a⁻¹ ⊣ Ra_*` on `D⁺`. -/
def plusDerivedAdjunction :
    plusInverseImageDerived J K ⊣ plusDirectImageDerived J K :=
  Adjunction.Derived.Plus.adjunction (inverseImageExact J K)
    (directImage J K.simplicial AddCommGrpCat.{max w u v})
    (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v})

/-- The canonical `D⁺` derived unit `E ⟶ Ra_* a⁻¹ E`. -/
abbrev plusDerivedUnit :
    𝟭 (DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w u v})) ⟶
      plusInverseImageDerived J K ⋙ plusDirectImageDerived J K :=
  (plusDerivedAdjunction J K).unit

end Plus

end CategoryTheory.SemiRepresentableFamily
