/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.Spectral
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 28.2.4: the underlying topological space of a quasi-compact and quasi-separated scheme
is spectral. -/
@[stacks 094L] #check
  (@AlgebraicGeometry.Scheme.instSpectralSpace :
    ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X], SpectralSpace X)
