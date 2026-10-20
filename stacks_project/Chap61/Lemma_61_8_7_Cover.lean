module

public import ReasLib.Algebra.WLocalIndEtale.Cover

@[expose] public section

universe u

/- The canonical w-local ind-étale cover is a ring type in the base universe. -/
#check (Algebra.WLocalIndEtale.Cover : ∀ (A : Type u) [CommRing A], Type u)
