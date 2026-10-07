module

public import Mathlib.RingTheory.LocalIso
public import ReasLib.RingTheory.RingHom.Local.Properties
import StacksCheckRecall

/- Lemma 61.3.2 (1): if A → B is a local isomorphism, then the base change
A' → B ⊗_A A' is a local isomorphism. Canonical owner:
`Algebra.IsLocalIso.instTensorProduct`. -/
@[stacks 096F] #check Algebra.IsLocalIso.instTensorProduct

/- Lemma 61.3.2 (2): if A → B identifies local rings, then the base change
A' → B ⊗_A A' identifies local rings. Canonical owner:
`RingHom.IsIsoOnLocalRings.isStableUnderBaseChange`. -/
@[stacks 096F] #check
  (RingHom.IsIsoOnLocalRings.isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.IsIsoOnLocalRings)
