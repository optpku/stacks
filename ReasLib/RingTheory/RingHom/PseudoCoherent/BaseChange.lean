/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.TorIndependent
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Flatness.Tor
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Basic

/-!
# Flat base change of pseudo-coherent ring maps

Pseudo-coherence of commutative ring maps is preserved by tensor-product base change along a
flat algebra.
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u

namespace RingHom.IsPseudoCoherentRingMap

/-- A pseudo-coherent commutative ring map remains pseudo-coherent after tensor-product base
change along a flat commutative algebra. -/
theorem baseChange_of_flat
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (hA : (algebraMap R A).IsPseudoCoherentRingMap)
    (hR' : (algebraMap R R').Flat) :
    (algebraMap R' (A ⊗[R] R')).IsPseudoCoherentRingMap := sorry

end RingHom.IsPseudoCoherentRingMap
