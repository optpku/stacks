module

public import ReasLib.RingTheory.Projective.NotLocallyFree
import StacksCheckRecall

@[expose] public section

universe u

namespace Module

/- Lemma 110.34.2: there exists a ring `R` and an ideal `I` such that `I` is
projective as an `R`-module but not locally free as an `R`-module. -/
@[stacks 05WJ] #check (Module.exists_ideal_projective_not_locallyFree :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R),
      Projective R I ∧ ¬ LocallyFree R I)

end Module
