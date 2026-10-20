/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

/-!
# Zariski Topology Recall

Both the topology and its standard opens are canonical `PrimeSpectrum` API.

@stack 00E1
-/

universe u

section

variable {R : Type u} [CommSemiring R]

/- Definition 10.17.3: the topology on `Spec(R)` whose closed subsets are the sets `V(T)` is the
canonical Zariski topology instance `PrimeSpectrum.zariskiTopology` on `PrimeSpectrum R`; the
textbook ring statement is its special case. -/
@[stacks 00E1 "(1) Zariski topology"]
#check @PrimeSpectrum.zariskiTopology

/- Definition 10.17.3: the standard open `D(f)` is the canonical
`PrimeSpectrum.basicOpen f`. -/
@[stacks 00E1 "(2) standard opens"]
#check @PrimeSpectrum.basicOpen

end
