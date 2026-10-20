/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Basic
import StacksCheckRecall

/-!
# Definition 15.82.4

@stack 065I
-/

@[expose] public section

/-!
# Definition 15.82.4 compatibility entry point

The reusable presentationwise relative pseudo-coherence predicates for
cochain complexes and modules are owned by
`ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative`.
-/

/- Definition 15.82.4 (1), tag `065I`: relative `m`-pseudo-coherent complexes. -/
@[stacks 065I "(1), relative m-pseudo-coherent complex"]
#check @CategoryTheory.CochainComplex.IsMPseudoCoherentRelativeTo

/- Definition 15.82.4 (2), tag `065I`: relative pseudo-coherent complexes. -/
@[stacks 065I "(2), relative pseudo-coherent complex"]
#check @CategoryTheory.CochainComplex.IsPseudoCoherentRelativeTo

/- Definition 15.82.4 (3), tag `065I`: relative `m`-pseudo-coherent modules. -/
@[stacks 065I "(3), relative m-pseudo-coherent module"]
#check @CategoryTheory.ModuleCat.IsMPseudoCoherentRelativeTo

/- Definition 15.82.4 (4), tag `065I`: relative pseudo-coherent modules. -/
@[stacks 065I "(4), relative pseudo-coherent module"]
#check @CategoryTheory.ModuleCat.IsPseudoCoherentRelativeTo
