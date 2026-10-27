/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Category
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a proper, flat morphism of finite presentation, the projection from relatively
perfect complexes on scheme-valued fibres with vanishing negative fibre self-Ext is a
stack in groupoids for the fppf topology. -/
@[stacks 0DLH]
instance instIsStackInGroupoids (f : X ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
