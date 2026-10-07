module

public import Mathlib.Algebra.Polynomial.Div
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank.PID
public import ReasLib.RingTheory.Polynomial.Equalizer.Finite
import StacksCheckRecall

/-!
# Restriction and generic-rank ingredients for Example 10.55.5

@stack 00JG

The former file-local restriction-of-scalars construction had no consumers.  The reusable
ingredients are the canonical polynomial divisibility and generic-rank APIs checked here.
-/

@[expose] public section

open CategoryTheory

@[stacks 00JG "polynomial divisibility"]
#check @Polynomial.X_dvd_iff

@[stacks 00JG "finite-module generic rank"]
#check @ModuleCat.K0.Finite.genericRank

@[stacks 00JG "generic rank on generators"]
#check @ModuleCat.K0.Finite.genericRank_of

@[stacks 00JG "generic-rank equivalence"]
#check @ModuleCat.K0.Finite.genericRankEquiv

@[stacks 00JG "common-endpoint evaluation"]
#check @Polynomial.EqualEndpoint.eval
