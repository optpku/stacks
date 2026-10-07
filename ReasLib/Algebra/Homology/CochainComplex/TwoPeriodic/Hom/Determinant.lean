module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Hom.Boundary
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant
public import ReasLib.Algebra.Module.End.FiniteLength

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism.Hom

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {K L : TwoPeriodicEndomorphism (ModuleCat.{v} R)}

/-- The periodic determinants of two acyclic finite-length complexes differ by the
finite-length determinant of the boundary automorphism
`boundaryIso f 1 ≪≫ (boundaryIso f 0).symm`. -/
theorem determinant_eq_boundary_mul
    (f : Hom K L) (hKlen : IsFiniteLength R K.X) (hLlen : IsFiniteLength R L.X)
    (hK : K.toCochainComplex.Acyclic) (hL : L.toCochainComplex.Acyclic)
    (hker : KernelDifferentialsVanish f) (hcoker : CokernelDifferentialsVanish f) :
    (determinant K hKlen hK : IsLocalRing.ResidueField R) =
      Module.End.finiteLengthDeterminant
          (boundaryAutomorphism f hK hL hker hcoker).hom.hom
          (cokernel_isFiniteLength f hLlen) *
        (determinant L hLlen hL : IsLocalRing.ResidueField R) := sorry

/-- The periodic determinants agree when the degree-zero and degree-one boundary
isomorphisms agree. -/
theorem determinant_eq_of_boundaryIso_eq
    (f : Hom K L) (hKlen : IsFiniteLength R K.X) (hLlen : IsFiniteLength R L.X)
    (hK : K.toCochainComplex.Acyclic) (hL : L.toCochainComplex.Acyclic)
    (hker : KernelDifferentialsVanish f) (hcoker : CokernelDifferentialsVanish f)
    (hboundary : boundaryIso f hK hL hker hcoker 0 =
      boundaryIso f hK hL hker hcoker 1) :
    (determinant K hKlen hK : IsLocalRing.ResidueField R) =
      (determinant L hLlen hL : IsLocalRing.ResidueField R) := sorry

end CategoryTheory.TwoPeriodicEndomorphism.Hom
