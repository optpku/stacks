/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-valued presheaves

For a category with the chaotic topology, modules over the inverse image of a ring `B` from the
point are canonically presented by `B`-module-valued presheaves.  This is the coefficient category
used by category homology and its derived tensor comparisons.
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace ModuleCat

/-- The category of `B`-module-valued presheaves on `C`; equivalently, the presheaf presentation
of `Mod(underline B)` when `C` carries the chaotic topology. -/
@[stacks 08PF "module presheaves on a category over a point"]
abbrev Presheaf (C : Type u) (B : Type w) [Category.{v} C] [Ring B] :=
  Cᵒᵖ ⥤ ModuleCat B

end ModuleCat
