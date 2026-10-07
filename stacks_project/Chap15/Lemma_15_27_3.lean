module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Tor
import StacksCheckRecall

/-!
# Eventual vanishing in ideal-power Tor systems

@stack 0911
-/

@[expose] public section

/- Lemma 15.27.3: in positive degree, maps between sufficiently separated
ideal-power Tor groups vanish uniformly for a finite module. -/
@[stacks 0911 "eventual vanishing of ideal-power Tor maps"]
#check @CategoryTheory.DerivedCategory.IdealPower.torPowerMap_eq_zero_eventually

#check @CategoryTheory.DerivedCategory.IdealPower.torSystem
#check @CategoryTheory.DerivedCategory.IdealPower.torSystem_transitionMap_eq_zero_eventually
