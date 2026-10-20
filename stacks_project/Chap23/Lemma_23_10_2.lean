/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Diagonal

@[expose] public section

/- Lemma 23.10.2 (tag `0FCX`): a flat finite-type map of Noetherian
rings is smooth when tensor-square multiplication has finite Tor dimension. -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable (f : A →+* B) (hfinite : f.FiniteType) (hflat : f.Flat)
variable (hdiag : f.DiagonalHasFiniteTorDimension)

@[stacks 0FCX]
#check (RingHom.Smooth.of_diagonal_hasFiniteTorDimension f hfinite hflat hdiag :
  f.Smooth)

end

#check @RingHom.DiagonalHasFiniteTorDimension
#check @RingHom.DiagonalIsPerfect
#check @RingHom.DiagonalIsPerfect.iff_hasFiniteTorDimension
#check @RingHom.Smooth.of_diagonal_isPerfect
#check @Algebra.Smooth.of_diagonal_isPerfect
#check @Algebra.Smooth.of_diagonal_hasFiniteTorDimension
