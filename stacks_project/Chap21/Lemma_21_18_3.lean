/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Composition.KFlat
import StacksCheckRecall

@[expose] public section

/-!
# Composition of derived pullbacks

The reusable API is currently stated for bundled morphisms between commutative ringed-site
presentations.  The source theorem is presentation-independent for morphisms of ringed topoi;
that stronger ambient formalization awaits a ringed-topos module category layer.
-/

/- Lemma 21.18.3 (0D6D), site-presented commutative form: for composable morphisms `f` and `g`,
the canonical comparison from `Lg^* ⋙ Lf^*` in Lean's functor order to `L(f.comp g)^*` is an
isomorphism. -/
@[stacks 0D6D]
#check @RingedSite.Hom.modulePullbackDerived.compComparison_isIso

#check @RingedSite.Hom.modulePullbackDerived.compComparison
#check @RingedSite.Hom.modulePullbackDerived.compComparison_counit
#check @RingedSite.Hom.modulePullbackDerived.compComparison_counit_app
#check @RingedSite.Hom.modulePullbackHomotopy.termwiseFlat
