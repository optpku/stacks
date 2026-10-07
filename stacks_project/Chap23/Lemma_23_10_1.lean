module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Diagonal

@[expose] public section

/- Lemma 23.10.1 (tag `0FCW`): a flat essentially finite-type local map
of Noetherian local rings is essentially smooth when tensor-square
multiplication has finite Tor dimension. -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable (f : A →+* B) [IsLocalHom f]
variable (hfinite : f.EssFiniteType) (hflat : f.Flat)
variable (hdiag : f.DiagonalHasFiniteTorDimension)

@[stacks 0FCW]
#check (RingHom.EssSmooth.of_diagonal_hasFiniteTorDimension f hfinite hflat hdiag :
  f.EssSmooth)

end

#check @RingHom.DiagonalHasFiniteTorDimension
#check @RingHom.DiagonalIsPerfect
#check @RingHom.DiagonalIsPerfect.iff_hasFiniteTorDimension
#check @RingHom.EssSmooth.of_diagonal_isPerfect
#check @Algebra.EssSmooth.of_diagonal_isPerfect
#check @Algebra.EssSmooth.of_diagonal_hasFiniteTorDimension
