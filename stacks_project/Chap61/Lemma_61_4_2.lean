module

public import ReasLib.RingTheory.RingHom.IndZariski.BaseChange
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u

/- Lemma 61.4.2: if ring maps `A → B` and `A → A'` are given, `B' = B ⊗[A] A'`
is the base change of `B`, and `A → B` is ind-Zariski, then `A' → B'` is
ind-Zariski. Canonical owner: `RingHom.IndZariski.baseChange`. -/
@[stacks 096P] #check (RingHom.IndZariski.baseChange :
  ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'],
    (algebraMap R A).IndZariski →
      (algebraMap R' (R' ⊗[R] A)).IndZariski)

#check @RingHom.IndZariski.isStableUnderBaseChange
#check @RingHom.IndZariski.Raw.baseChange
#check @RingHom.IndZariski.Raw.isStableUnderBaseChange
