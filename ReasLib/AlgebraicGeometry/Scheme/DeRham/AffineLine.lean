module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Affine
public import ReasLib.RingTheory.Kaehler.Polynomial

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- In positive characteristic, the degree-zero de Rham cohomology of the affine line over
`k` is not finite-dimensional over `k`. -/
theorem affineLineH0_not_finite (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] :
    ¬ Module.Finite k
      (affineCohomology (CommRingCat.ofHom (algebraMap k (Polynomial k))) 0) := sorry

/-- In positive characteristic, the degree-one de Rham cohomology of the affine line over
`k` is not finite-dimensional over `k`. -/
theorem affineLineH1_not_finite (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] :
    ¬ Module.Finite k
      (affineCohomology (CommRingCat.ofHom (algebraMap k (Polynomial k))) 1) := sorry

end AlgebraicGeometry.Scheme.DeRham
