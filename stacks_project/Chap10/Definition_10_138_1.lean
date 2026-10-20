/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.138.1

@stack 00TI
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.138.1: an `R`-algebra `S` is formally smooth if every `R`-algebra map
`S → A ⧸ I` lifts across the quotient map `A → A ⧸ I` whenever `I` is a square-zero ideal. -/
@[stacks 00TI "formally smooth predicate"]
#check @FormallySmooth

/- The infinitesimal lifting formulation of formal smoothness is the square-zero lifting criterion
for maps into quotient algebras `A ⧸ I`. -/
@[stacks 00TI "formal smooth lifting criterion"]
#check @FormallySmooth.iff_comp_surjective

end Algebra
