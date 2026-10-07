module

public import stacks_project.Chap61.Lemma_61_4_2_BaseChange
import StacksCheckRecall

@[expose] public section

/- Lemma 61.4.2: if ring maps `A → B` and `A → A'` are given, `B' = B ⊗[A] A'`
is the base change of `B`, and `A → B` is ind-Zariski, then `A' → B'` is
ind-Zariski. Canonical owner: `RingHom.IndZariski.baseChange`. -/
@[stacks 096P] #check @RingHom.IndZariski.baseChange

#check @RingHom.IndZariski.isStableUnderBaseChange
#check @RingHom.IndZariski.Raw.baseChange
