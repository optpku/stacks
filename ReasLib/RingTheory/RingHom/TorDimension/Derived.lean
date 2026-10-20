module

public import ReasLib.RingTheory.RingHom.TorDimension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude

/-!
# Derived characterization of ring-map Tor dimension

This leaf compares the intrinsic uniform `Tor`-vanishing predicates with the
degree-zero derived-tensor formulation.  Algebraic consumers can import the
lighter intrinsic owner without choosing a derived-tensor model.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring-map Tor-dimension bound is equivalent to the corresponding bound
for its target module in the canonical derived-category formulation. -/
theorem hasTorDimensionLE_iff_derived (f : R →+* S) (d : ℕ) :
    f.HasTorDimensionLE d ↔
      DerivedCategory.DerivedTensor.HasTorDimensionLE f.uliftMax.targetModule d := sorry

/-- Finite Tor dimension of a ring map is equivalent to finite Tor dimension
of its degree-zero target in the canonical derived-category formulation. -/
theorem hasFiniteTorDimension_iff_derived (f : R →+* S) :
    f.HasFiniteTorDimension ↔
      DerivedCategory.DerivedTensor.HasFiniteTorDimension
        ((DerivedCategory.singleFunctor (ModuleCat (ULift.{max u v} R)) 0).obj
          f.uliftMax.targetModule) := sorry

end RingHom
