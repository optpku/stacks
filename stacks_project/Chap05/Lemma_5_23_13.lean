/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.Sierpinski
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.13: the compact-open membership map gives the canonical
constructibly closed Sierpinski-product presentation of a spectral space. -/
@[stacks 09XW]
#check SpectralSpace.iff_homeomorphic_constructiblyClosed_sierpinskiProduct
