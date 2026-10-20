/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ConnectedComponents.Generalization
public import ReasLib.RingTheory.Spectrum.Prime.ConnectedComponents
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.6.28 (1): if `T` is a connected component of `Spec(A)`, equivalently
`T = connectedComponent x` for some `x` or `Maximal IsConnected T`, then `T` is
`StableUnderGeneralization`. -/
@[stacks 02DH]
#check (stableUnderGeneralization_connectedComponent :
    ∀ {R : Type u} [CommSemiring R] (x : PrimeSpectrum R),
      StableUnderGeneralization (connectedComponent x))

#check (stableUnderGeneralization_of_maximal_isConnected :
    ∀ {R : Type u} [CommSemiring R] {T : Set (PrimeSpectrum R)},
      Maximal IsConnected T → StableUnderGeneralization T)

/- Exercise 111.6.28 (2): if `A` is an `IsNoetherianRing` and `T` is a connected component of
`Spec(A)`, equivalently `T = connectedComponent x` or `Maximal IsConnected T`, then `T` is open
in `PrimeSpectrum A`. -/
@[stacks 02DH]
#check (PrimeSpectrum.isOpen_connectedComponent_of_isNoetherianRing :
    ∀ {R : Type u} [CommSemiring R] [IsNoetherianRing R] (x : PrimeSpectrum R),
      IsOpen (connectedComponent x))

#check (PrimeSpectrum.isOpen_of_maximal_isConnected_of_isNoetherianRing :
    ∀ {R : Type u} [CommSemiring R] [IsNoetherianRing R] {T : Set (PrimeSpectrum R)},
      Maximal IsConnected T → IsOpen T)

/- Exercise 111.6.28 (3): connected components of `Spec(ℕ → ZMod 2)` need not be open; this
spectrum consists of infinitely many closed points. -/
@[stacks 02DH]
#check (PrimeSpectrum.exists_connectedComponent_not_isOpen_piZModTwo :
    ∃ x : PrimeSpectrum (ℕ → ZMod 2), ¬ IsOpen (connectedComponent x))

#check (PrimeSpectrum.closedPoints_eq_univ_piZModTwo :
    closedPoints (PrimeSpectrum (ℕ → ZMod 2)) = Set.univ)

#check (PrimeSpectrum.infinite_closedPoints_piZModTwo :
    (closedPoints (PrimeSpectrum (ℕ → ZMod 2))).Infinite)
