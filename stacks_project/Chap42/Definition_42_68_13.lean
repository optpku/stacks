module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant
import StacksCheckRecall

universe u v

/- Definition 42.68.13: the determinant of an exact finite-length two-periodic complex over a
local ring is the signed determinant of its canonical comparison `γψ ∘ σ ∘ γφ⁻¹`. -/
@[stacks 02PJ] #check (CategoryTheory.TwoPeriodicEndomorphism.determinant :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    (K : CategoryTheory.TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic),
    (IsLocalRing.ResidueField R)ˣ)
