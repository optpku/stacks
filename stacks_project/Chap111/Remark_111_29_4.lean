module

public import ReasLib.RingTheory.Polynomial.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open Polynomial

/- Remark 111.29.4 (1): if `h ∈ ℤ[X]` is monic of degree `d` with `0 < d`, then the map
`ℤ[X] →+* ℤ[X]` sending `X` to `h` is finite locally free of rank `d`. -/
@[stacks 02ER] #check
  (Polynomial.aeval_finiteLocallyFreeOfRank (R := ℤ) :
    ∀ {d : ℕ} {h : ℤ[X]}, h.IsMonicOfDegree d → 0 < d →
      ((aeval h : ℤ[X] →ₐ[ℤ] ℤ[X]).toRingHom).FiniteLocallyFreeOfRank d)

/- Remark 111.29.4 (2): if `h ∈ ℤ[X]` is monic of degree `d` with `0 < d`, then for every
prime `p` the map `(ZMod p)[X] →+* (ZMod p)[X]` sending `X` to
`h.map (Int.castRingHom (ZMod p))` is finite locally free of rank `d`. -/
@[stacks 02ER] #check
  (Polynomial.aeval_zmod_finiteLocallyFreeOfRank :
    ∀ {d : ℕ} {h : ℤ[X]}, h.IsMonicOfDegree d → 0 < d → ∀ {p : ℕ}, Nat.Prime p →
      ((aeval (h.map (Int.castRingHom (ZMod p))) :
          (ZMod p)[X] →ₐ[ZMod p] (ZMod p)[X]).toRingHom).FiniteLocallyFreeOfRank d)
