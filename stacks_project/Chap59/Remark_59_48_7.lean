/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ClosedImmersion
import StacksCheckRecall

@[expose] public section

/- Remark 59.48.7: In the fppf case, the lifting step used for the other
topologies is unavailable in general. Given a ring `A`, an ideal `I`, and a
faithfully flat, finitely presented map `A / I ⟶ B̄`, there is no reason to
expect a flat, finitely presented map `A ⟶ B` with `B / I B ≠ 0` such that
`A / I ⟶ B / I B` factors through `B̄`. Thus the proof for the other
topologies does not work for the fppf topology. The source asks whether some
closed immersion has non-exact big fppf pushforward on abelian sheaves; this
is an open question, not an established counterexample. -/
@[stacks 04C5] #check
  (AlgebraicGeometry.Scheme.Fppf.Big.existsNonexactPushforwardForClosedImmersion : Prop)
