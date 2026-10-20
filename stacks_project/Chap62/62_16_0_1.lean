/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Hilbert
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] (r : ℕ)

/- 62.16.0.1: Let `f : X ⟶ S` be a morphism of schemes of finite presentation.
Let `r ≥ 0`. Denote `Hilb(X/S, r)` the set of closed subschemes `Z ⊂ X` such
that `Z ⟶ S` is flat, of finite presentation, and of relative dimension `≤ r`.
The group homomorphism
`FreeAbelianGroup (f.HilbertClosedSubscheme r) →+ f.FiberCycleFamily (r : ℤ)`
sends `∑ nᵢ [Zᵢ]` to `∑ nᵢ [Zᵢ/X/S]ᵣ`. -/
@[stacks 0H6V]
#check (AlgebraicGeometry.Scheme.Hom.hilbertCycleClass f r :
  FreeAbelianGroup (f.HilbertClosedSubscheme r) →+
    f.FiberCycleFamily (r : ℤ))
