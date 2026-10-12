/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GlobalDimension.ResidueField
import StacksCheckRecall

/-!
# Residue-Field Projective Dimension and the Cotangent Space

@stack 00OA
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Lemma 10.110.3 (Stacks `00OA`): for a Noetherian local ring, the projective dimension of its
residue field is at least the residue-field dimension of its cotangent space. -/
@[stacks 00OA]
#check (IsLocalRing.finrank_cotangentSpace_le_projectiveDimension_residueField (R := R) :
  Module.finrank (ResidueField R) (CotangentSpace R) ≤
    projectiveDimension (ModuleCat.of R (ResidueField R)))

#check (IsLocalRing.not_hasProjectiveDimensionLT_finrank_cotangentSpace (R := R) :
  ¬ HasProjectiveDimensionLT
      (ModuleCat.of R (ResidueField R))
      (Module.finrank (ResidueField R) (CotangentSpace R)))
