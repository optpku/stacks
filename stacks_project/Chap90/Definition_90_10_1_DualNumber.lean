module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.DualNumber
public import ReasLib.RingTheory.DualNumber.Finiteness
public import ReasLib.RingTheory.DualNumber.Residue
public import stacks_project.Chap90.Definition_90_16_8_Predeformation

/-!
# Dual numbers as an object of `ArtinianLocalAlgCat`

The dual numbers `DualNumber k` bundle as the object `k[ε]` of `C_Λ`, together with the
canonical projection onto the residue field `k`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt
open scoped DualNumber

universe u

/-- Dual numbers over a field are Artinian. -/
instance isArtinianRing_dualNumber {k : Type u} [Field k] : IsArtinianRing (DualNumber k) :=
  IsArtinianRing.of_finite k (DualNumber k)

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The residue-field identification of `DualNumber k` with `k`, obtained from the first
isomorphism theorem for the coefficient projection along the explicit right inverse `inl`. -/
def dualNumberResidueFieldIso : ResidueField (DualNumber k) ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (DualNumber.maximalIdeal_eq_span_singleton_eps.trans
        (DualNumber.epsIdeal_eq_span k).symm)).trans
    ((DualNumber.residueAlgEquiv k).restrictScalars Λ)

/-- The residue identification of `k[ε]` sends the class of a dual number to its scalar
coefficient. -/
theorem dualNumberResidueFieldIso_apply (x : DualNumber k) :
    dualNumberResidueFieldIso Λ k (IsLocalRing.residue (DualNumber k) x) = x.fst := sorry

/-- The dual numbers `DualNumber k`, viewed as an object of `ArtinianLocalAlgCat Λ k`. -/
def dualNumber : ArtinianLocalAlgCat Λ k :=
  of (DualNumber k) (dualNumberResidueFieldIso Λ k)

/-- The bundled dual-number object has carrier `DualNumber k`. -/
theorem dualNumber_carrier : (dualNumber Λ k).carrier = DualNumber k := sorry

/-- The canonical projection `k[ε] ⟶ k` in `ArtinianLocalAlgCat`. -/
def dualNumberToResidue : dualNumber Λ k ⟶ residue Λ k where
  hom := (fstHom k k k).restrictScalars Λ
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `dualNumberToResidue` is the coefficient projection. -/
theorem dualNumberToResidue_hom :
    (dualNumberToResidue Λ k).hom = (fstHom k k k).restrictScalars Λ := sorry

/-- The projection `k[ε] ⟶ k` is surjective. -/
theorem dualNumberToResidue_surjective :
    Function.Surjective (dualNumberToResidue Λ k).hom := sorry

/-- The projection `k[ε] ⟶ k` is a local `Λ`-algebra map compatible with residue
identifications. -/
theorem dualNumberToResidue_spec :
    IsLocalHom (dualNumberToResidue Λ k).hom ∧
      (residue Λ k).residueFieldIso.toAlgHom.comp
          (ResidueField.mapAlgHom (dualNumberToResidue Λ k).hom) =
        (dualNumber Λ k).residueFieldIso.toAlgHom := sorry

end ArtinianLocalAlgCat
