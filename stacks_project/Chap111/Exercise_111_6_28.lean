module

public import stacks_project.Chap111.Exercise_111_6_28_Generalization
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.Topology.Noetherian.Basic
import StacksCheckRecall

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Exercise 111.6.28 (1): if `T` is a connected component of `Spec(A)`, equivalently
`T = connectedComponent x` for some `x` or `Maximal IsConnected T`, then `T` is
`StableUnderGeneralization`. -/
@[stacks 02DH]
theorem stableUnderGeneralization_connectedComponent {R : Type u} [CommSemiring R]
    (x : PrimeSpectrum R) :
    StableUnderGeneralization (connectedComponent x) := sorry

/-- A connected component of `Spec(A)`, in the maximal-connected-subset sense, is stable under
generalization. -/
theorem stableUnderGeneralization_of_maximal_isConnected {R : Type u} [CommSemiring R]
    {T : Set (PrimeSpectrum R)} (hT : Maximal IsConnected T) :
    StableUnderGeneralization T := sorry

/-- Exercise 111.6.28 (2): if `A` is an `IsNoetherianRing` and `T` is a connected component of
`Spec(A)`, equivalently `T = connectedComponent x` or `Maximal IsConnected T`, then `T` is open
in `PrimeSpectrum A`. -/
@[stacks 02DH]
theorem isOpen_connectedComponent_of_isNoetherianRing {R : Type u} [CommSemiring R]
    [IsNoetherianRing R] (x : PrimeSpectrum R) :
    IsOpen (connectedComponent x) := sorry

/-- If `A` is an `IsNoetherianRing`, a connected component of `Spec(A)` in the
maximal-connected-subset sense is open. -/
theorem isOpen_of_maximal_isConnected_of_isNoetherianRing {R : Type u} [CommSemiring R]
    [IsNoetherianRing R] {T : Set (PrimeSpectrum R)} (hT : Maximal IsConnected T) :
    IsOpen T := sorry

/-- On `Spec(ℕ → ZMod 2)`, every point is closed. -/
theorem closedPoints_eq_univ_piZModTwo :
    closedPoints (PrimeSpectrum (ℕ → ZMod 2)) = Set.univ := sorry

/-- `Spec(ℕ → ZMod 2)` has infinitely many closed points. -/
theorem infinite_closedPoints_piZModTwo :
    (closedPoints (PrimeSpectrum (ℕ → ZMod 2))).Infinite := sorry

/-- Exercise 111.6.28 (3): connected components of `Spec(ℕ → ZMod 2)` need not be open; this
spectrum consists of infinitely many closed points. -/
@[stacks 02DH]
theorem exists_connectedComponent_not_isOpen_piZModTwo :
    ∃ x : PrimeSpectrum (ℕ → ZMod 2), ¬ IsOpen (connectedComponent x) := sorry

end PrimeSpectrum

/- Companion: connected components are always closed. -/
#check @isClosed_connectedComponent

/- Companion: connected components are open in a locally connected space. -/
#check @isOpen_connectedComponent

/- Companion: the spectrum of a Noetherian ring is a Noetherian space. -/
#check @PrimeSpectrum.instNoetherianSpace

/- Companion: every open set is stable under generalization. -/
#check @IsOpen.stableUnderGeneralization

/- Companion: a subset is a connected component iff it is a maximal connected subset. -/
#check @maximal_isConnected_iff_eq_connectedComponent
