/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import stacks_project.Chap99.Lemma_99_10_1_Picard

/-!
# Picard stack of a morphism of algebraic spaces

The category of invertible modules on fibres of `f : X ⟶ B`, bundled as a
stack in groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Picard projection is a stack in groupoids on `(Sch/S)_fppf`. -/
theorem p_isStack (f : X ⟶ B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Picard

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Picard stack of a morphism of algebraic spaces, as a stack in groupoids
over `(Sch/S)_fppf`. -/
def picardStack (f : X ⟶ B) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjectionWith (Scheme.fppfTopology.over S) (Picard.p f)
    (Picard.p_isStack f)

/-- The projection of `picardStack f` is the Picard projection to `(Sch/S)_fppf`. -/
theorem picardStack_p (f : X ⟶ B) :
    (picardStack f).p = Picard.p f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
