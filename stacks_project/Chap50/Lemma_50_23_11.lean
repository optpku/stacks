/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.RationalPoint
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

/- Lemma 50.23.11: the Hodge Gysin image of `1` along a rational point of an irreducible
smooth proper `d`-dimensional scheme over a field is nonzero. -/
@[stacks 0G8E]
#check (AlgebraicGeometry.Scheme.DeRham.Gysin.rationalPointFundamentalClass_ne_zero :
  ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IrreducibleSpace X.left] [IsProper X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (x : 𝟙_ (AlgebraicGeometry.SchemeOverField k) ⟶ X),
    AlgebraicGeometry.Scheme.DeRham.Gysin.rationalPointFundamentalClass X d x ≠ 0)

end
