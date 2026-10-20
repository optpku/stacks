module

public import stacks_project.Chap85.Lemma_85_13_2_System
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites

/- Lemma 85.13.2 (1): in Situation 85.3.3, an object K of D(C_total) yields the
simplicial system (K_n, K(φ)) of the derived category, with K_n the restriction of
K to D(C_n) and K(φ) : f_φ⁻¹ K_m ⟶ K_n in D(C_n). -/
@[stacks 0D9H] #check @toDerivedSystem

/- Lemma 85.13.2 (2): if K is cartesian, so is that system. -/
@[stacks 0D9H] #check @toDerivedSystem_isCartesian
