module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.DualNumber
public import ReasLib.RingTheory.DualNumber.Finiteness
public import ReasLib.RingTheory.DualNumber.Residue
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Dual numbers as an object of `ArtinianLocalAlgCat`

The dual numbers `DualNumber k` bundle as the object `k[ε]` of `C_Λ`, together with the
canonical identification of the residue field with `k`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt
open scoped DualNumber

universe u

namespace DualNumber

/-- Dual numbers over a field are an Artinian ring. -/
instance instIsArtinianRing {k : Type u} [Field k] : IsArtinianRing (DualNumber k) :=
  IsArtinianRing.of_finite k (DualNumber k)

end DualNumber

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The residue-field identification of `DualNumber k` with `k`, obtained by comparing the
maximal ideal with `DualNumber.epsIdeal` and restricting `DualNumber.residueAlgEquiv` from
`k` to `Λ`. -/
def dualNumberResidueFieldIso : ResidueField (DualNumber k) ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (DualNumber.maximalIdeal_eq_span_singleton_eps.trans
        (DualNumber.epsIdeal_eq_span k).symm)).trans
    ((DualNumber.residueAlgEquiv k).restrictScalars Λ)

/-- The residue identification of `k[ε]` sends the class of a dual number to its scalar
coefficient. -/
theorem dualNumberResidueFieldIso_apply (x : DualNumber k) :
    dualNumberResidueFieldIso Λ k (residue (DualNumber k) x) = x.fst := sorry

/-- The dual numbers `DualNumber k`, viewed as an object of `ArtinianLocalAlgCat Λ k`. -/
def dualNumber : ArtinianLocalAlgCat Λ k :=
  of (DualNumber k) (dualNumberResidueFieldIso Λ k)

/-- The bundled dual-number object has carrier `DualNumber k`. -/
theorem dualNumber_carrier : (dualNumber Λ k).carrier = DualNumber k := sorry

/-- The dual-number object of `C_Λ` is Artinian local with the canonical residue identification
of `ResidueField (DualNumber k)` with `k`. -/
theorem dualNumber_spec :
    IsLocalRing (dualNumber Λ k).carrier ∧
      IsArtinianRing (dualNumber Λ k).carrier ∧
      (dualNumber Λ k).residueFieldIso = dualNumberResidueFieldIso Λ k := sorry

end ArtinianLocalAlgCat
