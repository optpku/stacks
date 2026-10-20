/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import ReasLib.Algebra.Homology.CochainComplex.Projective.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-projectivity of fixed-amplitude projective complexes

The fixed-amplitude owner already supplies its upper support bound and termwise projectivity as
instances.  This leaf turns exactly those facts into the canonical K-projective instance without
making the underlying object-property module depend on homotopy-category infrastructure.
@stack 0A5N
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.ProjectiveIn

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {a b : ℤ}

/-- A fixed-amplitude complex of projective objects is canonically K-projective. -/
@[stacks 0A5N "K-projectivity of bounded projective representatives"]
instance isKProjective (P : ProjectiveIn C a b) :
    P.obj.IsKProjective := sorry

end CochainComplex.ProjectiveIn
