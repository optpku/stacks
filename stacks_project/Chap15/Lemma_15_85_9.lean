/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
import StacksCheckRecall

/-!
# Lemma 15.85.9

The source transfer statement is owned by
`CategoryTheory.twoTermExtOneAnnihilatedByIdeal_of_h0_iso_of_hneg1_epi`, using the canonical
Ext-annihilation predicate from the preceding two-term owner.

@stack 0G9J
-/

@[expose] public section

open CategoryTheory

universe u

@[stacks 0G9J "Lemma 15.85.9"]
#check fun {R : Type u} [CommRing R] (I : Ideal R)
    {K K' : DerivedCategory (ModuleCat R)} (α : K ⟶ K')
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hK'GE : K'.IsGE (-1)) (hK'LE : K'.IsLE 0)
    (hα0 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map α))
    (hαneg1 : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).map α))
    (hI : CategoryTheory.twoTermExtOneAnnihilatedByIdeal K I) =>
  (CategoryTheory.twoTermExtOneAnnihilatedByIdeal_of_h0_iso_of_hneg1_epi
      I α hKGE hKLE hK'GE hK'LE hα0 hαneg1 hI :
    CategoryTheory.twoTermExtOneAnnihilatedByIdeal K' I)

#check fun {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) (I : Ideal R) =>
  (CategoryTheory.twoTermExtOneAnnihilatedByIdeal K I : Prop)
