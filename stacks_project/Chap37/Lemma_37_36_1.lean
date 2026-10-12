/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.MinimalPrime.FilteredColimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v

/- Lemma 37.36.1: for a filtered colimit of commutative rings with faithfully flat transition
maps, the extended-natural cardinality of the minimal-prime set is the supremum of the stage
cardinalities. -/
@[stacks 0CB3]
#check (_root_.minimalPrimes.encard_eq_iSup_of_isColimit :
  ∀ {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{max u v}) (c : Cocone F) (_ : IsColimit c),
    (∀ {i j : J} (f : i ⟶ j), (F.map f).hom.FaithfullyFlat) →
      (_root_.minimalPrimes c.pt).encard =
        ⨆ i : J, (_root_.minimalPrimes (F.obj i)).encard)
