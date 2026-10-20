/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Adjunction.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃ w

namespace CategoryTheory

open Limits

/-- A morphism of topoi `Sh(K) ⟶ Sh(J)` presented by sites: a left-exact adjunction between
the sheaf categories. -/
@[stacks 00XA]
abbrev MorphismOfTopoiIn
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) :=
  LeftExactAdjunction (Sheaf K (Type w)) (Sheaf J (Type w))

namespace MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Textbook notation for the inverse and direct image functors of a morphism
of topoi. -/
scoped notation:100 f "⁻¹" => LeftExactAdjunction.inverseImage f
scoped notation:100 f "_*" => LeftExactAdjunction.pushforward f

/-- The inverse image of a morphism of topoi preserves finite limits. -/
theorem inverseImage_preservesFiniteLimits (f : MorphismOfTopoiIn J K) :
    PreservesFiniteLimits f.inverseImage := sorry

section Terminal

variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- Inverse image along a morphism of topoi preserves the chosen terminal
type-valued sheaf. -/
noncomputable def inverseImageTerminalIso
    (f : MorphismOfTopoiIn JD JC) :
    f.inverseImage.obj
        (Sheaf.terminal JD Types.isTerminalPUnit : Sheaf JD (Type w)) ≅
      (Sheaf.terminal JC Types.isTerminalPUnit : Sheaf JC (Type w)) :=
  LeftExactAdjunction.inverseImageTerminalIso f
    (Sheaf.isTerminalTerminal JD Types.isTerminalPUnit)
    (Sheaf.isTerminalTerminal JC Types.isTerminalPUnit)

/-- The terminal comparison's forward map is the unique map to the terminal sheaf. -/
@[simp]
theorem inverseImageTerminalIso_hom (f : MorphismOfTopoiIn JD JC) :
    f.inverseImageTerminalIso.hom =
      (Sheaf.isTerminalTerminal JC Types.isTerminalPUnit).from
        (f.inverseImage.obj
          (Sheaf.terminal JD Types.isTerminalPUnit : Sheaf JD (Type w))) := by
  rfl

end Terminal

/-- The identity morphism of the topos Sh(C, J). -/
def id (J : GrothendieckTopology C) : MorphismOfTopoiIn J J :=
  LeftExactAdjunction.id _

/-- Composition of topos morphisms. -/
def comp {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    (f : MorphismOfTopoiIn J K) (g : MorphismOfTopoiIn K L) : MorphismOfTopoiIn J L :=
  LeftExactAdjunction.comp f g

/-- A topos morphism is an embedding when its direct image is fully faithful. -/
abbrev IsEmbedding (f : MorphismOfTopoiIn J K) : Prop :=
  LeftExactAdjunction.IsEmbedding f

end MorphismOfTopoiIn

end CategoryTheory
