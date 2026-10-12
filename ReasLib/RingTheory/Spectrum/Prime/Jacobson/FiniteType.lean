/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.JacobsonSpace
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed points under finite type maps

A finite type map from a Jacobson ring contracts closed points to closed points, and the induced
residue-field extensions are finite.

@stack 00GB
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

open Set Topology

section Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsJacobsonRing R] [Algebra.FiniteType R S]

/-- A maximal point of a finite type algebra over a Jacobson ring contracts to a maximal point. -/
theorem comap_asIdeal_isMaximal_of_isMaximal (x : PrimeSpectrum S)
    (hx : x.asIdeal.IsMaximal) :
    (comap (algebraMap R S) x).asIdeal.IsMaximal := sorry

/-- Proposition 10.35.19 (2) (Tag 00GB): a finite type map from a Jacobson ring sends closed
points to closed points. -/
@[stacks 00GB "(2)"]
theorem comap_mapsTo_closedPoints :
    Set.MapsTo (comap (algebraMap R S))
      (closedPoints (PrimeSpectrum S)) (closedPoints (PrimeSpectrum R)) := sorry

/-- Proposition 10.35.19 (3) (Tag 00GB): the residue-field extension at a maximal point of a
finite type algebra over a Jacobson ring is finite. -/
@[stacks 00GB "(3)"]
theorem moduleFinite_residueField_of_isMaximal (x : PrimeSpectrum S)
    (hx : x.asIdeal.IsMaximal) :
    (Ideal.ResidueField.map (comap (algebraMap R S) x).asIdeal x.asIdeal
      (algebraMap R S) rfl).Finite := sorry

/-- The residue-field extension at a closed point of a finite type algebra over a Jacobson ring is
finite. -/
theorem moduleFinite_residueField_of_mem_closedPoints (x : PrimeSpectrum S)
    (hx : x ∈ closedPoints (PrimeSpectrum S)) :
    (Ideal.ResidueField.map (comap (algebraMap R S) x).asIdeal x.asIdeal
      (algebraMap R S) rfl).Finite := sorry

end Algebra

section RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsJacobsonRing R]

/-- A finite type ring homomorphism over a Jacobson ring sends closed points to closed points. -/
theorem comap_mapsTo_closedPoints_of_finiteType (f : R →+* S) (hf : f.FiniteType) :
    Set.MapsTo (comap f) (closedPoints (PrimeSpectrum S)) (closedPoints (PrimeSpectrum R)) := sorry

/-- The map on spectra induced by a finite type ring homomorphism, restricted to closed points. -/
def comapClosedPoints (f : R →+* S) (hf : f.FiniteType) :
    closedPoints (PrimeSpectrum S) → closedPoints (PrimeSpectrum R) :=
  (comap_mapsTo_closedPoints_of_finiteType f hf).restrict (comap f)
    (closedPoints (PrimeSpectrum S)) (closedPoints (PrimeSpectrum R))

/-- The underlying point of `comapClosedPoints f hf x` is the contraction of `x`. -/
@[simp] theorem val_comapClosedPoints (f : R →+* S) (hf : f.FiniteType)
    (x : closedPoints (PrimeSpectrum S)) :
    ((comapClosedPoints f hf x : closedPoints (PrimeSpectrum R)) : PrimeSpectrum R) = comap f x :=
  sorry

end RingHom

end PrimeSpectrum
