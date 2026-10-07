module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Cohomology
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Koszul
public import ReasLib.RingTheory.Sequence.Koszul.Regularity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech cohomology of Koszul-regular families

A Koszul-regular finite family makes the extended alternating Cech complex
cohomologically concentrated in its top degree.

@stack 0G6L
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace LocalizedModule.Away.Cech.Alternating.Cohomology

variable {R : Type u} [CommRing R]

/-- Lemma 15.31.1 (Stacks tag `0G6L`): the extended alternating
Cech complex of a Koszul-regular family has zero cohomology outside its top degree. -/
@[stacks 0G6L "Lemma 15.31.1"]
theorem isZero_of_isKoszulRegularSequence {r : ℕ} (f : Fin r → R)
    (h : RingTheory.Sequence.IsKoszulRegularSequence f) (q : ℕ) (hq : q ≠ r) :
    IsZero ((Alternating.extended f R).homology q) := sorry

end LocalizedModule.Away.Cech.Alternating.Cohomology
