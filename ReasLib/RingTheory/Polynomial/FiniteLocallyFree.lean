module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import ReasLib.RingTheory.RingHom.FiniteLocallyFree

@[expose] public section

universe u

namespace Polynomial

/-- Monic polynomial substitution of positive degree is finite locally free of that degree. -/
theorem aeval_finiteLocallyFreeOfRank {R : Type u} [CommRing R] {d : ℕ} {h : R[X]}
    (hh : h.IsMonicOfDegree d) (hd : 0 < d) :
    ((aeval h : R[X] →ₐ[R] R[X]).toRingHom).FiniteLocallyFreeOfRank d := sorry

/-- Reduction of monic polynomial substitution modulo a prime is finite locally free of the
same degree. -/
theorem aeval_zmod_finiteLocallyFreeOfRank {d : ℕ} {h : ℤ[X]}
    (hh : h.IsMonicOfDegree d) (hd : 0 < d) {p : ℕ} (hp : Nat.Prime p) :
    ((aeval (h.map (Int.castRingHom (ZMod p))) :
        (ZMod p)[X] →ₐ[ZMod p] (ZMod p)[X]).toRingHom).FiniteLocallyFreeOfRank d := sorry

end Polynomial
