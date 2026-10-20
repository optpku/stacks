/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Groupoid

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import stacks_project.Chap65.Lemma_65_16_3
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap94.Lemma_94_16_1_KernelPair
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

import StacksCheckRecall

/-! # Kernel-pair groupoid source compatibility -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The selected algebraic space representing a groupoid fibration. -/
abbrev representingSpace {S : Scheme.{u}} {Y : GroupoidsOver S}
    (hY : IsRepresentableByAlgebraicSpace Y) : AlgebraicSpace S :=
  IsRepresentableByAlgebraicSpace.representingSpace hY

/-- The equivalence to the selected representing algebraic space. -/
abbrev representingEquiv {S : Scheme.{u}} {Y : GroupoidsOver S}
    (hY : IsRepresentableByAlgebraicSpace Y) : Y ≌ (representingSpace hY).toGroupoids :=
  IsRepresentableByAlgebraicSpace.representingEquiv hY

/-- Regard an algebraic space over a scheme as a space over the identity base space. -/
abbrev overS {S : Scheme.{u}} : AlgebraicSpace S ⥤ Over (ofOver (Over.mk (𝟙 S))) :=
  extendBaseOver (𝟙 S)

/-- Evaluation of a morphism between presheaf fibrations recovers the original morphism. -/
abbrev evalMapIso {S : Scheme.{u}} {F G : AlgebraicSpace S}
    (ψ : F.toGroupoids ⟶ G.toGroupoids) :
    ψ ≅ toGroupoids.map (toGroupoids.eval ψ) := toGroupoids.evalMapIso ψ

end AlgebraicGeometry.AlgebraicStack

/- Lemma 94.16.1 (4): arbitrary representing spaces inherit the kernel-pair groupoid. -/
@[stacks 04T4] #check (AlgebraicGeometry.AlgebraicStack.groupoidWith :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    {FU FR : AlgebraicSpace S},
    (U ≌ FU.toGroupoids) →
    (KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) →
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))))
