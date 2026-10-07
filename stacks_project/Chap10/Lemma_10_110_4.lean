module

public import ReasLib.RingTheory.GlobalDimension.ResidueField
import StacksCheckRecall

/-!
# Finite Residue-Field Projective Dimension

@stack 00OB
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Lemma 10.110.4 (Stacks `00OB`): if the residue field of a Noetherian local ring has
projective dimension `n`, then `n` is bounded by the Krull dimension of the ring. -/
@[stacks 00OB]
#check (IsLocalRing.projectiveDimension_residueField_le_ringKrullDim (R := R) :
  ∀ {n : ℕ},
    projectiveDimension (ModuleCat.of R (ResidueField R)) = n →
      n ≤ ringKrullDim R)

#check (IsLocalRing.projectiveDimension_residueField_le_ringKrullDim_of_ne_top (R := R) :
  projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤ →
    projectiveDimension (ModuleCat.of R (ResidueField R)) ≤ ringKrullDim R)
