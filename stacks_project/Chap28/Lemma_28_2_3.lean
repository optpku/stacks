/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Constructible
import StacksCheckRecall

@[expose] public section

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} [QuasiSeparatedSpace X]

/- Lemma 28.2.3 (1): the intersection of two quasi-compact open subsets of a
quasi-separated scheme is quasi-compact. -/
@[stacks 054D] #check
  (QuasiSeparatedSpace.inter_isCompact (α := X) :
    ∀ U V : Set X,
      IsOpen U → IsCompact U → IsOpen V → IsCompact V → IsCompact (U ∩ V))

/- Lemma 28.2.3 (2): every quasi-compact open subset of a quasi-separated scheme
is retrocompact. -/
@[stacks 054D] #check
  (IsCompact.isRetrocompact (X := X) :
    ∀ {U : Set X}, IsCompact U → IsOpen U → IsRetrocompact U)
