module

public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
import StacksCheckRecall

/-!
# Isolated points in fibres

@stack 00PK

The fibre spectrum and residue-field algebra are canonical `PrimeSpectrum` /
`Ideal.ResidueField` constructions.  The numbered entry retains the ambient
basic-open clause as a source-facing bridge.
-/

@[expose] public section

universe u v

open PrimeSpectrum
open TopologicalSpace
open scoped PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

-- Local declaration justification (source-local instance): the residue-field action is chosen for
-- this specific fiber point; registering it globally would create competing scalar structures.
noncomputable local instance fiberPrimeResidueFieldAlgebra
    (p : PrimeSpectrum R) (qbar : PrimeSpectrum (p.asIdeal.Fiber S)) :
  Algebra p.asIdeal.ResidueField qbar.asIdeal.ResidueField :=
  Ideal.ResidueField.algebraOfLiesOver p.asIdeal qbar.asIdeal

/- Lemma 10.122.2 (00PK): for a finite type map `R → S`, a prime `q` over
`p`, and the corresponding fiber point `qbar`, the six isolated-point,
fiber-localization, ambient basic-open, dimension, closed-point, and residue-
field conditions are equivalent. -/
@[stacks 00PK "source six-clause form"]
#check fun (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) => show
  let qbar : PrimeSpectrum (p.asIdeal.Fiber S) :=
    PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩
  List.TFAE
    [ IsOpen ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber S)))
    , Module.Finite p.asIdeal.ResidueField (Localization.AtPrime qbar.asIdeal)
    , ∃ g : S, g ∉ q.asIdeal ∧
        ({q' : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q' = p} ∩
          (D(g) : Set (PrimeSpectrum S)) = ({q} : Set (PrimeSpectrum S)))
    , topologicalKrullDimAt qbar = 0
    , IsClosed ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber S))) ∧
        ringKrullDim (Localization.AtPrime qbar.asIdeal) = 0
    , Module.Finite p.asIdeal.ResidueField qbar.asIdeal.ResidueField ∧
        ringKrullDim (Localization.AtPrime qbar.asIdeal) = 0
    ] from by sorry

/-! Canonical fibre owners used by the source-facing bridge. -/

@[stacks 00PK "fiber-prime equivalence"]
#check @PrimeSpectrum.preimageEquivFiber

@[stacks 00PK "fiber-prime homeomorphism"]
#check @PrimeSpectrum.preimageHomeomorphFiber

@[stacks 00PK "quasi-finiteness under base change"]
#check @Algebra.QuasiFiniteAt.baseChange

end
