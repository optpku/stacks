/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Purity
public import ReasLib.RingTheory.Normal.Ring
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Torsion.Free

@[expose] public section

open AlgebraicGeometry
open scoped ENat

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- For a regular local ring of Krull dimension at least two, restriction of finite
étale covers to the punctured spectrum is essentially surjective. -/
instance hasPurity_of_regularLocalRing
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    [hdim : Fact (2 ≤ ringKrullDim A)] :
    HasPurity A := sorry

/-- A finite normal torsion-free algebra over a regular local ring of Krull dimension
at least two is étale if its spectrum is étale over the punctured spectrum. -/
theorem etale_of_finite_normal
    {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] [IsNormalRing B] [Module.IsTorsionFree A B]
    (hdim : 2 ≤ ringKrullDim A)
    (hU : Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_ puncturedOpen A)) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A B))) := sorry

end AlgebraicGeometry.PuncturedSpectrum
