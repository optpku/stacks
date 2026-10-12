/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Hom.Determinant
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism.Hom

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {K L : TwoPeriodicEndomorphism (ModuleCat.{v} R)}

/- Lemma 42.68.25: the periodic determinants of two acyclic finite-length complexes differ by
the finite-length determinant of the canonical boundary automorphism. -/
@[stacks 02PV]
#check (CategoryTheory.TwoPeriodicEndomorphism.Hom.determinant_eq_boundary_mul :
  (f : Hom K L) →
    (hKlen : IsFiniteLength R K.X) → (hLlen : IsFiniteLength R L.X) →
    (hK : K.toCochainComplex.Acyclic) → (hL : L.toCochainComplex.Acyclic) →
    (hker : KernelDifferentialsVanish f) → (hcoker : CokernelDifferentialsVanish f) →
    (determinant K hKlen hK : IsLocalRing.ResidueField R) =
      Module.End.finiteLengthDeterminant
          (boundaryAutomorphism f hK hL hker hcoker).hom.hom
          (cokernel_isFiniteLength f hLlen) *
        (determinant L hLlen hL : IsLocalRing.ResidueField R))

/- The in-particular clause identifies the periodic determinants when the two boundary
isomorphisms agree. -/
#check (CategoryTheory.TwoPeriodicEndomorphism.Hom.determinant_eq_of_boundaryIso_eq :
  (f : Hom K L) →
    (hKlen : IsFiniteLength R K.X) → (hLlen : IsFiniteLength R L.X) →
    (hK : K.toCochainComplex.Acyclic) → (hL : L.toCochainComplex.Acyclic) →
    (hker : KernelDifferentialsVanish f) → (hcoker : CokernelDifferentialsVanish f) →
    boundaryIso f hK hL hker hcoker 0 = boundaryIso f hK hL hker hcoker 1 →
    (determinant K hKlen hK : IsLocalRing.ResidueField R) =
      (determinant L hLlen hL : IsLocalRing.ResidueField R))

end CategoryTheory.TwoPeriodicEndomorphism.Hom
