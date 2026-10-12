/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sober.OpenCover
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.8.8

Cover-local sober-space API is owned by `ReasLib.Topology.Sober.OpenCover`.
-/

/- Lemma 5.8.8 (1): the Kolmogorov property is local on locally closed covers. -/
@[stacks 06N9 "Kolmogorov spaces are local on locally closed covers"]
#check @t0Space_iff_forall_of_locallyClosed_cover

/- Lemma 5.8.8 (2): quasi-sobriety is local on open covers in Mathlib. -/
@[stacks 06N9 "quasi-sober spaces are local on open covers"]
#check @TopologicalSpace.IsOpenCover.quasiSober_iff_forall

/- Lemma 5.8.8 (3): the Kolmogorov component is local on open covers. -/
@[stacks 06N9 "Kolmogorov spaces are local on open covers"]
#check @TopologicalSpace.IsOpenCover.t0Space_iff_forall

/- Lemma 5.8.8 (3): sobriety is local on open covers. -/
@[stacks 06N9 "sober spaces are local on open covers"]
#check @TopologicalSpace.IsOpenCover.sober_iff_forall
