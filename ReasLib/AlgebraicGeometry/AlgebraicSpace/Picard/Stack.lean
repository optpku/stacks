/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.FiberIsoClasses
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# The Picard stack of a morphism of algebraic spaces

The Picard projection is a stack in groupoids for the fppf topology, and its
fibers are essentially small.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Picard projection of a morphism of algebraic spaces over `S` is a stack
in groupoids for the fppf topology on schemes over `S`. -/
instance isStackInGroupoids (f : X ⟶ B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f) := sorry

/-- Every fiber of the Picard projection over a scheme over `S` is essentially
`u`-small. -/
instance fibers_essentiallySmall (f : X ⟶ B) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((p f).Fiber U)) := sorry

/-- The Picard projection to schemes over the target is a stack in groupoids
for the relative fppf topology. -/
instance toSchemesOver_isStackInGroupoids (f : X ⟶ B) :
    IsStack.InGroupoids (SchemesOver.fppfTopology B) (toSchemesOver f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Picard stack of a morphism of algebraic spaces, as a stack in groupoids
for the fppf topology on schemes over the base scheme. -/
noncomputable def picardStack {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjectionWith (Scheme.fppfTopology.over S) (Picard.p f)
    (Picard.isStackInGroupoids f)

end AlgebraicGeometry.AlgebraicSpace
