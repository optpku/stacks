module

public import ReasLib.RingTheory.MvPolynomial.FrobeniusGraph

#check (MvPolynomial.FrobeniusGraph.Coord)
#check (MvPolynomial.FrobeniusGraph.specialize :
  ∀ p : ℕ, MvPolynomial MvPolynomial.FrobeniusGraph.Coord ℤ →+*
    MvPolynomial (Fin 2) (ZMod p))
#check (MvPolynomial.FrobeniusGraph.specialize_C :
  ∀ (p : ℕ) (a : ℤ),
    MvPolynomial.FrobeniusGraph.specialize p (MvPolynomial.C a) =
      MvPolynomial.C (Int.castRingHom (ZMod p) a))
#check (MvPolynomial.FrobeniusGraph.specialize_X_x :
  ∀ p : ℕ,
    MvPolynomial.FrobeniusGraph.specialize p (MvPolynomial.X .x) =
      MvPolynomial.X (0 : Fin 2))
#check (MvPolynomial.FrobeniusGraph.specialize_X_y :
  ∀ p : ℕ,
    MvPolynomial.FrobeniusGraph.specialize p (MvPolynomial.X .y) =
      MvPolynomial.X (1 : Fin 2))
#check (MvPolynomial.FrobeniusGraph.specialize_X_u :
  ∀ p : ℕ,
    MvPolynomial.FrobeniusGraph.specialize p (MvPolynomial.X .u) =
      MvPolynomial.X (0 : Fin 2) ^ p)
#check (MvPolynomial.FrobeniusGraph.specialize_X_v :
  ∀ p : ℕ,
    MvPolynomial.FrobeniusGraph.specialize p (MvPolynomial.X .v) =
      MvPolynomial.X (1 : Fin 2) ^ p)
#check (MvPolynomial.FrobeniusGraph.specialize_apply :
  ∀ (p : ℕ) (f : MvPolynomial MvPolynomial.FrobeniusGraph.Coord ℤ)
    (xy : Fin 2 → ZMod p),
    MvPolynomial.eval xy (MvPolynomial.FrobeniusGraph.specialize p f) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun
        | .x => xy 0
        | .y => xy 1
        | .u => xy 0 ^ p
        | .v => xy 1 ^ p) f)
