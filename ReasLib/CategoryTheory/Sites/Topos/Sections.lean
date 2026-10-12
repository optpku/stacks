/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.InternalModule
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u₀ v₀ u₁ v₁ w

namespace CategoryTheory.Sheaf

/-- Compatible sections are precisely maps from the constant singleton sheaf. -/
noncomputable def sectionsTerminalHomEquiv
    {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
    (F : Sheaf J (Type w)) :
    F.obj.sections ≃ (Sheaf.terminal J Types.isTerminalPUnit ⟶ F) where
  toFun s := ⟨F.obj.sectionsEquivHom PUnit s⟩
  invFun h := (F.obj.sectionsEquivHom PUnit).symm h.hom
  left_inv := sorry
  right_inv := sorry

end CategoryTheory.Sheaf

namespace CategoryTheory.MorphismOfTopoiIn

variable {C₀ : Type u₀} [Category.{v₀} C₀] {J₀ : GrothendieckTopology C₀}
variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
variable (f : MorphismOfTopoiIn.{u₀, u₁, v₀, v₁, w} J₀ J₁)

/-- Inverse image carries the singleton sheaf to a terminal sheaf; the
comparison is the unique isomorphism between these two terminal objects. -/
noncomputable def inverseImageTerminalIso :
    f.inverseImage.obj (Sheaf.terminal J₀ Types.isTerminalPUnit) ≅
      Sheaf.terminal J₁ Types.isTerminalPUnit :=
  ((Sheaf.isTerminalTerminal J₀ Types.isTerminalPUnit).isTerminalObj
      f.inverseImage _).uniqueUpToIso
    (Sheaf.isTerminalTerminal J₁ Types.isTerminalPUnit)

/-- The canonical direct-image global-section equivalence. Its maps are
adjoint transposes transported through the terminal-object comparison. -/
noncomputable def pushforwardSectionsEquiv (F : Sheaf J₁ (Type w)) :
    (f.pushforward.obj F).obj.sections ≃ F.obj.sections where
  toFun s := (Sheaf.sectionsTerminalHomEquiv F).symm
    (f.inverseImageTerminalIso.inv ≫
      (f.adjunction.homEquiv _ _).symm
        (Sheaf.sectionsTerminalHomEquiv (f.pushforward.obj F) s))
  invFun s := (Sheaf.sectionsTerminalHomEquiv (f.pushforward.obj F)).symm
    ((f.adjunction.homEquiv _ _)
      (f.inverseImageTerminalIso.hom ≫ Sheaf.sectionsTerminalHomEquiv F s))
  left_inv := sorry
  right_inv := sorry

end CategoryTheory.MorphismOfTopoiIn
