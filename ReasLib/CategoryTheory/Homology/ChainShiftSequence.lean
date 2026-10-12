/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.ChainShift
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of Shifted Chain Complexes

This module equips chain homology with its canonical shift sequence.  The construction first
reads a chain complex as a cochain complex by negating degrees, uses the cochain-homology shift
sequence, and then transports the resulting homology objects back to the chain convention.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex

universe v u

namespace ChainComplex

noncomputable section

variable (C : Type u) [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

namespace Homology

namespace ShiftSequence

/-- On the pullback shift owner, degree `i` chain homology is degree `-i` cochain homology. -/
abbrev pullbackFunctor (i : ℤ) : cochainShiftPullback C ⥤ C :=
  homologyFunctor C (up ℤ) (-i)

/-- The shift comparison for homology on the cochain category with shifts pulled back along
integer negation. -/
noncomputable def pullbackShiftIso (k i i' : ℤ) (hi' : k + i = i') :
    shiftFunctor (cochainShiftPullback C) k ⋙ pullbackFunctor C i ≅
      pullbackFunctor C i' :=
    Functor.isoWhiskerRight
      (CategoryTheory.pullbackShiftIso (CochainComplex C ℤ)
        (negAddMonoidHom : ℤ →+ ℤ) k (-k) rfl)
      (homologyFunctor C (up ℤ) (-i)) ≪≫
    CochainComplex.ShiftSequence.shiftIso C (-k) (-i) (-i')
      ((Int.neg_add).symm.trans (congrArg Neg.neg hi'))

variable {C}

/-- The canonical comparison from cochain homology after degree negation to chain homology. -/
noncomputable def comparisonApp (K : ChainComplex C ℤ) (i : ℤ) :
    (pullbackFunctor C i).obj ((chainToCochain C).obj K) ≅
      (homologyFunctor C (down ℤ) i).obj K :=
  ((((chainToCochain C).obj K).restrictionHomologyIso
      embeddingDownIntUpInt (i + 1) i (i - 1)
      ((down ℤ).prev_eq' (down_mk (i + 1) i rfl))
      ((down ℤ).next_eq' (down_mk i (i - 1) (sub_add_cancel i 1)))
      ((embeddingDownIntUpInt_f (i + 1)).trans Int.neg_add)
      (embeddingDownIntUpInt_f i)
      ((embeddingDownIntUpInt_f (i - 1)).trans <|
        (Int.neg_sub i 1).trans <| (sub_eq_add_neg 1 i).trans <| add_comm 1 (-i))
      ((up ℤ).prev_eq' (up_mk (-i - 1) (-i) (sub_add_cancel (-i) 1)))
      ((up ℤ).next_eq' (up_mk (-i) (-i + 1) rfl))).symm) ≪≫
    (homologyFunctor C (down ℤ) i).mapIso ((chainCochainEquiv C).unitIso.app K).symm

/-- The degree-negation comparison for homology is natural in the chain complex. -/
theorem comparisonApp_naturality {K L : ChainComplex C ℤ} (f : K ⟶ L) (i : ℤ) :
    (pullbackFunctor C i).map ((chainToCochain C).map f) ≫
        (comparisonApp L i).hom =
      (comparisonApp K i).hom ≫ (homologyFunctor C (down ℤ) i).map f := sorry

variable (C)

/-- Reindexing by negation intertwines pullback cochain homology and ordinary chain homology. -/
noncomputable def comparison (i : ℤ) :
    chainToCochain C ⋙ pullbackFunctor C i ≅ homologyFunctor C (down ℤ) i :=
  NatIso.ofComponents (fun K ↦ comparisonApp K i)
    (fun f ↦ comparisonApp_naturality f i)

/-- The natural shift comparison on chain homology, expressed using the standard chain-homology
functors rather than the intermediate pullback cochain-homology functors. -/
noncomputable def shiftIso (k i i' : ℤ) (hi' : k + i = i') :
    shiftFunctor (ChainComplex C ℤ) k ⋙ homologyFunctor C (down ℤ) i ≅
      homologyFunctor C (down ℤ) i' :=
  Functor.isoWhiskerLeft _ (comparison C i).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((chainToCochain C).commShiftIso k) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pullbackShiftIso C k i i' hi') ≪≫
    comparison C i'

/-- Chain homology carries a shift sequence whose degree-`i` term is definitionally the standard
functor `homologyFunctor C (down ℤ) i`. -/
noncomputable instance instChain :
    (homologyFunctor C (down ℤ) 0).ShiftSequence ℤ where
  sequence := fun i ↦ homologyFunctor C (down ℤ) i
  isoZero := Iso.refl _
  shiftIso := shiftIso C
  shiftIso_zero := sorry
  shiftIso_add := sorry

variable {C}

/-- The chain-homology shift identification with an explicitly specified target degree. -/
noncomputable def isoOfEq (K : ChainComplex C ℤ) (k i i' : ℤ)
    (hi' : k + i = i') :
    K.homology i' ≅ (K⟦k⟧).homology i :=
  ((homologyFunctor C (down ℤ) 0).shiftIso k i i' hi').app K |>.symm

/-- The canonical identification `K.homology (i + k) ≅ (K⟦k⟧).homology i`. -/
@[stacks 011B]
noncomputable def iso (K : ChainComplex C ℤ) (k i : ℤ) :
    K.homology (i + k) ≅ (K⟦k⟧).homology i :=
  isoOfEq K k i (i + k) (add_comm k i)

end ShiftSequence

end Homology

end

end ChainComplex
