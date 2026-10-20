/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.Product
import StacksCheckRecall

@[expose] public section

/- Lemma 5.23.10: products of spectral spaces are spectral. -/
@[stacks 0907]
#check SpectralSpace.prod
