/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

@[expose] public section

/-!
# Exact Products Indexed by Countable Types

`CountableAB4Star` is phrased using small countable index types.  This module exposes its exactness
consequence uniformly for countable types in any universe.
-/

open CategoryTheory.Limits

universe v u uI

namespace CategoryTheory.HasExactLimitsOfShape

/-- Exact countable products remain exact after transporting a countable indexing type between
universes. -/
instance (priority := 100) of_countableAB4Star
    {C : Type u} [Category.{v} C] [HasCountableProducts C] [CountableAB4Star C]
    (I : Type uI) [Countable I] :
    HasExactLimitsOfShape (Discrete I) C := sorry

end CategoryTheory.HasExactLimitsOfShape
