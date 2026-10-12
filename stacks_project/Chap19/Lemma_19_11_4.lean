/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.BoundedObjects
import StacksCheckRecall

@[expose] public section

/-!
# Bounded Objects in Grothendieck Abelian Categories

The quotient presentation and essential-smallness infrastructure is owned by ReasLib. This file
records the two assertions of Lemma 19.11.4 as complete typed checks.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/- Lemma 19.11.4 (1): an object with at most `kappa` subobjects is a quotient of a coproduct of
at most `kappa` copies of a chosen generator. -/
@[stacks 079E "bounded coproduct quotient"] #check
  fun (C : Type u) [Category.{v} C] [Abelian C]
      [IsGrothendieckAbelian.{max u v} C]
      (U M : C) (hU : IsSeparator U) (kappa : Cardinal.{max u v})
      (hM : ObjectProperty.subobjectCardinalLE kappa M) ↦
    (IsSeparator.existsEpiFromCoproduct hU M kappa hM :
      ∃ (alpha : Type (max u v)) (_ : Cardinal.mk alpha ≤ kappa)
        (f : (∐ fun _ : alpha ↦ U) ⟶ M), Epi f)

/- Lemma 19.11.4 (2): the objects with at most `kappa` subobjects form an essentially small
object property. -/
@[stacks 079E "bounded isomorphism classes form a set"] #check
  fun (C : Type u) [Category.{v} C] [Abelian C]
      [IsGrothendieckAbelian.{w} C] (kappa : Cardinal.{max u v})
      [Small.{w} kappa.out] ↦
    (inferInstance : ObjectProperty.EssentiallySmall.{w}
      (ObjectProperty.subobjectCardinalLE (C := C) kappa))

/- Lemma 19.11.4 (2), source formulation: essential smallness supplies a set containing exactly
one representative of every bounded isomorphism class. -/
#check fun (C : Type u) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] (kappa : Cardinal.{max u v})
    [Small.{w} kappa.out] ↦
  (ObjectProperty.EssentiallySmall.exists_set_representatives
    (ObjectProperty.subobjectCardinalLE (C := C) kappa) :
      ∃ S : Set C,
        (∀ X ∈ S, Cardinal.mk (Subobject X) ≤ kappa) ∧
        ∀ X : C, Cardinal.mk (Subobject X) ≤ kappa →
          ∃! Y : C, Y ∈ S ∧ Nonempty (Y ≅ X))

#check @Cardinal.LowerInitialSegment
#check @ObjectProperty.quotientRepresentatives
#check @ObjectProperty.subobjectCardinalLE
#check @ObjectProperty.SubobjectCardinal.essentiallySmall_le

end CategoryTheory
