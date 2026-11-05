/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import ReasLib.Topology.Sheaves.Abelian
public import ReasLib.Topology.Sheaf.Zero

/-!
# Abelian structure on sheaf categories

Re-exports the abelian-category structure on sheaves, together with the canonical homology
structure carried by every abelian category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}}

end TopCat.Sheaf
