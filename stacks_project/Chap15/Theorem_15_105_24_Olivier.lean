module

public import ReasLib.RingTheory.Etale.Weakly.StrictHenselian
import StacksCheckRecall

/-!
# Olivier's theorem for weakly etale local maps

This file records Theorem 15.105.24 (Olivier), Stacks `092Z`, through the shared strictly
henselian weakly etale owner.

@stack 092Z
-/

@[expose] public section

-- The epimorphism step used in Olivier's theorem.
@[stacks 092Z "Theorem 15.105.24 (Olivier), epimorphism step"]
#check @Algebra.WeaklyEtale.isEpi_of_isLocalHom_of_strictHenselianLocalRing

-- Theorem 15.105.24 (Olivier): a weakly etale local homomorphism from a strictly henselian local
-- ring to a local ring is bijective.
@[stacks 092Z "Theorem 15.105.24 (Olivier)"]
#check @Algebra.WeaklyEtale.algebraMap_bijective_of_isLocalHom_of_strictHenselianLocalRing
