module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Noetherian.Defs

@[expose]
public section

universe u v w

namespace KaehlerDifferential

/-- For a commutative algebra surjecting onto a field finite over a Noetherian
base, the canonical conormal sequence is exact at the differential fiber and
its map to the residue-field differentials is surjective. -/
theorem residueConormalSequence_exact (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [IsNoetherianRing Λ] [CommRing A] [Field k]
    [Algebra Λ A] [Algebra A k] [Algebra Λ k] [IsScalarTower Λ A k]
    [Module.Finite Λ k] (h_surjective : Function.Surjective (algebraMap A k)) :
    Function.Exact (KaehlerDifferential.kerCotangentToTensor Λ A k)
      (KaehlerDifferential.mapBaseChange Λ A k) ∧
    Function.Surjective (KaehlerDifferential.mapBaseChange Λ A k) := sorry

end KaehlerDifferential
