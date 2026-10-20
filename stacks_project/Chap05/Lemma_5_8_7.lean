/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sober.LocallyClosed
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.8.7

Locally closed subspace sobriety API is owned by
`ReasLib.Topology.Sober.LocallyClosed`.
-/

/- Lemma 5.8.7 (1): every subspace of a Kolmogorov space is Kolmogorov. -/
@[stacks 0B31 "Kolmogorov subspaces inherit T0 separation"]
#check @Subtype.t0Space

/- Lemma 5.8.7 (2): a locally closed subspace of a quasi-sober space is quasi-sober. -/
@[stacks 0B31 "locally closed subspaces inherit quasi-sobriety"]
#check @IsLocallyClosed.quasiSober

/- Lemma 5.8.7 (3): a locally closed subspace of a sober space is sober. -/
@[stacks 0B31 "locally closed subspaces inherit sobriety"]
#check @IsLocallyClosed.sober
