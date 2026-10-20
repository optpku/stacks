module

public import ReasLib.RingTheory.KrullDimension.FlatLocal
import StacksCheckRecall

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsDomain A] [IsDomain B]
variable [IsLocalRing A] [IsLocalRing B]

/- Lemma 37.52.3: for an injective flat essentially finite-type local map of
domains, the closed-fiber dimension plus the residue-field transcendence degree
is the transcendence degree of the map. -/
@[stacks 053T] #check
  (RingHom.DimensionFormula.closedFiber_add_residueTrdeg_eq_trdeg :
    ∀ (f : A →+* B) [IsLocalHom f], Function.Injective f → f.EssFiniteType → f.Flat →
      -- Local instance justification (defeq pin): `f.toAlgebra` identifies `algebraMap A B` for the residue-field and transcendence-degree terms.
      letI : Algebra A B := f.toAlgebra
      ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map f) +
          (Cardinal.toNat
            (Algebra.trdeg (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :
            WithBot ℕ∞) =
        (Cardinal.toNat (Algebra.trdeg A B) : WithBot ℕ∞))

end
