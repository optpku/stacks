/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.ProperDimensionOne
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 53.2.4: a morphism from a proper scheme of dimension at most one over a field to a
separated scheme is finite if its restriction to every one-dimensional irreducible component is
nonconstant. -/
@[stacks 0CCL] #check
  (AlgebraicGeometry.Scheme.Hom.isFinite_of_dimLEOne_of_nonconstant_irreducibleComponents :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
      [IsSeparated Y.hom] [IsProper X.hom] (f : X ⟶ Y)
      (hdim : topologicalKrullDim X.left ≤ 1)
      (hcomponent : ∀ Z : irreducibleComponents X.left,
        topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1 →
          (X.left.irreducibleComponentSubschemeι Z ≫ f.left).IsNonconstant),
      IsFinite f.left)
