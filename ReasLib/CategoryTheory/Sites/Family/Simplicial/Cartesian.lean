/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Augmentation

/-!
# Cartesian pullbacks along total localization
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor

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

/-- A sheaf on `(C / K)_total` is cartesian when every simplex-operator comparison
`F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an isomorphism. -/
abbrev IsCartesian (G : Sheaf (overSiteTotalTopology J K) A) : Prop :=
  Grothendieck.Sheaf.IsCartesian (overSiteDiagram K) (overSitePrecoverage J K) A G

/-- Cartesianness on `(C / K)_total` is equivalent to every `F(φ)` being an isomorphism. -/
theorem isCartesian_iff (G : Sheaf (overSiteTotalTopology J K) A) :
    IsCartesian J K A G ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (Grothendieck.Sheaf.sheafTransition
          (overSiteDiagram K) (overSitePrecoverage J K) A φ G) :=
  Grothendieck.Sheaf.isCartesian_iff (overSiteDiagram K) (overSitePrecoverage J K) A G

/-- The object property of being a cartesian sheaf on `(C / K)_total`. -/
abbrev cartesianProperty : ObjectProperty (Sheaf (overSiteTotalTopology J K) A) :=
  Grothendieck.Sheaf.cartesianProperty (overSiteDiagram K) (overSitePrecoverage J K) A

/-- The category of cartesian sheaves on `(C / K)_total`. -/
abbrev Cartesian :=
  Grothendieck.Sheaf.Cartesian (overSiteDiagram K) (overSitePrecoverage J K) A

/-- The underlying sheaf of an object of `Cartesian` is cartesian. -/
theorem cartesian_isCartesian (G : Cartesian J K A) : IsCartesian J K A G.obj :=
  G.property

/-- Inverse image `a⁻¹` along `j_total` of a sheaf on `C`. -/
abbrev inverseImage : Sheaf J A ⥤ Sheaf (overSiteTotalTopology J K) A :=
  (totalForget K).sheafPushforwardContinuous A (overSiteTotalTopology J K) J

/-- `inverseImage` is continuous sheaf pushforward of `j_total`. -/
theorem inverseImage_eq :
    inverseImage J K A =
      (totalForget K).sheafPushforwardContinuous A (overSiteTotalTopology J K) J :=
  rfl

/-- Pullback of a sheaf along total localization has invertible fiber comparisons. -/
instance inverseImage_isCartesian (F : Sheaf J A) :
    Grothendieck.Sheaf.IsCartesian (overSiteDiagram K) (overSitePrecoverage J K) A
      (((totalForget K).sheafPushforwardContinuous A
        (overSiteTotalTopology J K) J).obj F) :=
  sorry

variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ A,
    (totalForget K).op.HasPointwiseRightKanExtension P]

/-- Direct image `a_*` along `j_total` of a sheaf on `(C / K)_total`. -/
abbrev directImage : Sheaf (overSiteTotalTopology J K) A ⥤ Sheaf J A :=
  (totalForget K).sheafPushforwardCocontinuous A (overSiteTotalTopology J K) J

/-- `directImage` is cocontinuous sheaf pushforward of `j_total`. -/
theorem directImage_eq :
    directImage J K A =
      (totalForget K).sheafPushforwardCocontinuous A (overSiteTotalTopology J K) J :=
  rfl

end CategoryTheory.SemiRepresentableFamily
