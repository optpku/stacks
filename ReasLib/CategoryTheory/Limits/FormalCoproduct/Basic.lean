/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic

/-!
# Basic API for formal coproducts

This leaf provides neutral notation-level accessors for formal coproduct data.  It is independent
of fixed-target families, sites, and presheaves.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- The indexing type carried by a formal coproduct. -/
abbrev index (K : FormalCoproduct.{w} C) : Type w := K.I

end CategoryTheory.Limits.FormalCoproduct

