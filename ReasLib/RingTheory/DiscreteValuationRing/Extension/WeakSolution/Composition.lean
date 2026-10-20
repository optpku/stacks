module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ascent and descent of weak solutions

This module owns the four tower clauses of Lemma 15.116.4.  The chapter entry is a thin,
source-traceable recall; downstream developments can import this file directly.

@stack 09ES
-/

open FieldExtension.TensorProduct

universe u v w x y z t

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type z} {K1 : Type t}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra B M] [Algebra C M] [Algebra K M] [Algebra L M]
variable [IsFractionRing C M]
variable [IsScalarTower A C M] [IsScalarTower A K M]
variable [IsScalarTower B C M] [IsScalarTower B L M]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

/-- Lemma 15.116.4 (1): a weak solution for `A ⟶ C` descends to `A ⟶ B`. -/
@[stacks 09ES "Lemma 15.116.4 (1)"]
theorem weakSolutionFor_of_weakSolutionFor_comp
    (hK1 : IsWeakSolutionFor A C K M K1) :
    IsWeakSolutionFor A B K L K1 := sorry
-- Proof strategy: for a branch `p ⊂ q` of the intermediate normalization, use lying over to
-- choose a maximal branch `r` of the top normalization above `q`; identify the localized maps as
-- the tower `(A₁)_p ⟶ (B₁)_q ⟶ (C₁)_r`, then descend ramification index one from
-- `hK1.branch_spec` by multiplicativity of ramification indices.

/-- Lemma 15.116.4 (2): a solution for `A ⟶ C` descends to `A ⟶ B`. -/
@[stacks 09ES "Lemma 15.116.4 (2)"]
theorem solutionFor_of_solutionFor_comp
    (hK1 : IsSolutionFor A C K M K1) :
    IsSolutionFor A B K L K1 := sorry
-- Proof strategy: choose the same lifted branch chain `p ⊂ q ⊂ r`; use the adic formal-smooth
-- characterization by weak unramifiedness and separable residue fields, descend both conditions
-- from the composite localized map, and conclude with `IsSolutionFor.iff_forall_ideals`.

/-- Lemma 15.116.4 (3): weak solutions compose when every reduced tensor-product factor is a weak
solution for `B ⟶ C`. -/
@[stacks 09ES "Lemma 15.116.4 (3)"]
theorem weakSolutionFor_comp_of_weakSolutionFor_of_reducedTensorProductFactors
    (hAB : IsWeakSolutionFor A B K L K1)
    (hBC :
      ∀ m : MaximalSpectrum (reduced K L K1),
        DVR.BaseChange.IsWeakSolutionOnFactor (B := B) (C := C) (K := K) (L := L) (M := M)
          (K1 := K1) m) :
    IsWeakSolutionFor A C K M K1 := sorry
-- Proof strategy: contract a chosen top branch `r` to a maximal intermediate branch `q`, then to
-- its coordinate `m : MaximalSpectrum (reduced K L K1)` under the finite-product decomposition.
-- Apply `hAB` on `p ⊂ q`, transport `hBC m` to `q ⊂ r`, and compose the two localized weakly
-- unramified maps by ramification-index multiplicativity.

/-- Lemma 15.116.4 (4): solutions compose when every reduced tensor-product factor is a solution
for `B ⟶ C`. -/
@[stacks 09ES "Lemma 15.116.4 (4)"]
theorem solutionFor_comp_of_solutionFor_of_reducedTensorProductFactors
    (hAB : IsSolutionFor A B K L K1)
    (hBC :
      ∀ m : MaximalSpectrum (reduced K L K1),
        DVR.BaseChange.IsSolutionOnFactor (B := B) (C := C) (K := K) (L := L) (M := M)
          (K1 := K1) m) :
    IsSolutionFor A C K M K1 := sorry
-- Proof strategy: use the same branch contraction and factor-coordinate transport as in the weak
-- theorem; obtain formal smoothness on `p ⊂ q` from `hAB` and on `q ⊂ r` from `hBC m`, then
-- compose weak ramification and residue-field separability through the localized DVR tower.

end
