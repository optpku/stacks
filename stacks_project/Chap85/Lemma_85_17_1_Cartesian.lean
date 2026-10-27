/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Cartesian

/-!
# Cartesian sheaves on a fiberwise total site

A sheaf on the Grothendieck total site of a fiberwise simplicial site is cartesian when every
simplex-operator comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an isomorphism. The declarations are owned by the shared mathematical library.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor

noncomputable section

universe u v w

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))
variable (A : Type (max w u v + 1)) [Category.{max w u v} A]
variable [HasWeakSheafify J A]
variable [HasWeakSheafify (overSiteTotalTopology J K) A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K n).toGrothendieck A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K n).toGrothendieck (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology J K) (Type (max w u v))]

#check (CategoryTheory.SemiRepresentableFamily.IsCartesian J K A :
  Sheaf (overSiteTotalTopology J K) A → Prop)

#check (CategoryTheory.SemiRepresentableFamily.isCartesian_iff J K A :
  ∀ G : Sheaf (overSiteTotalTopology J K) A,
    IsCartesian J K A G ↔ ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      IsIso (Grothendieck.Sheaf.sheafTransition
        (overSiteDiagram K) (overSitePrecoverage J K) A φ G))

#check (CategoryTheory.SemiRepresentableFamily.cartesianProperty J K A :
  ObjectProperty (Sheaf (overSiteTotalTopology J K) A))

#check (CategoryTheory.SemiRepresentableFamily.Cartesian J K A :
  Type (max w u v + 1))

#check (CategoryTheory.SemiRepresentableFamily.cartesian_isCartesian J K A :
  ∀ G : Cartesian J K A, IsCartesian J K A G.obj)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage J K A :
  Sheaf J A ⥤ Sheaf (overSiteTotalTopology J K) A)

#check (CategoryTheory.SemiRepresentableFamily.inverseImage_eq J K A :
  inverseImage J K A =
    (totalForget K).sheafPushforwardContinuous A (overSiteTotalTopology J K) J)

variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ A,
    (totalForget K).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.SemiRepresentableFamily.directImage J K A :
  Sheaf (overSiteTotalTopology J K) A ⥤ Sheaf J A)

#check (CategoryTheory.SemiRepresentableFamily.directImage_eq J K A :
  directImage J K A =
    (totalForget K).sheafPushforwardCocontinuous A (overSiteTotalTopology J K) J)

end CategoryTheory.SemiRepresentableFamily
