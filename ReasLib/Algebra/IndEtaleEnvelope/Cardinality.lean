/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import ReasLib.Algebra.IndEtaleEnvelope.Iteration

/-!
# Cardinality bounds for ind-étale envelopes

The finite stages, their indexing set, the ind-étale envelope, and its
sequential iteration are bounded by any infinite cardinal bounding the base
ring.
-/

@[expose] public section

universe u v

open scoped Cardinal
open CategoryTheory Limits

namespace Algebra.IndEtaleEnvelope

/-- The standard-smooth presentations of a commutative ring have cardinality
at most any infinite cardinal bounding the ring. -/
theorem mk_presentation_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    #(Presentation A) ≤ κ := by
  let f : Presentation A → Σ n : ℕ, Fin n → MvPolynomial (Fin n) A :=
    fun P ↦ ⟨P.n, P.relations⟩
  have hf : Function.Injective f := by
    rintro ⟨n, relations, hu, hff⟩ ⟨n', relations', hu', hff'⟩ h
    cases h
    rfl
  refine (Cardinal.mk_le_of_injective hf).trans ?_
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun n : ℕ ↦ #(Fin n → MvPolynomial (Fin n) A)) ≤
        Cardinal.sum (fun _ : ℕ ↦ κ) := by
      refine Cardinal.sum_le_sum _ _ fun n ↦ ?_
      have hp : #(MvPolynomial (Fin n) A) ≤ κ := by
        refine MvPolynomial.cardinalMk_le_max_lift.trans ?_
        exact sup_le (sup_le (by simpa using hA)
          (by simpa using (Cardinal.natCast_le_aleph0 (n := n)).trans hκ)) hκ
      calc
        #(Fin n → MvPolynomial (Fin n) A) =
            #(MvPolynomial (Fin n) A) ^ (n : Cardinal) := by
          simp
        _ ≤ κ ^ (n : Cardinal) := Cardinal.power_le_power_right hp
        _ ≤ κ := Cardinal.power_nat_le hκ
    _ = ℵ₀ * κ := by simp
    _ ≤ κ := Cardinal.mul_le_of_le hκ hκ le_rfl

/-- The finite-subset index of the standard-smooth presentations has
cardinality at most any infinite cardinal bounding the ring. -/
theorem mk_index_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    #(Index A) ≤ κ := by
  classical
  calc
    #(Index A) = #(Finset (Presentation A)) :=
      Cardinal.mk_congr OrderIso.finsetSetFinite.symm.toEquiv
    _ ≤ #(List (Presentation A)) :=
      Cardinal.mk_le_of_surjective List.toFinset_surjective
    _ ≤ max ℵ₀ #(Presentation A) := Cardinal.mk_list_le_max _
    _ ≤ κ := max_le hκ (mk_presentation_le A hκ hA)

/-- Every finite stage of the ind-étale envelope has cardinality at most any
infinite cardinal bounding the base ring. -/
theorem mk_stage_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) (E : Index A) :
    #(stage E) ≤ κ := by
  letI : Fintype E.1 := E.2.fintype
  calc
    #(stage E) ≤ #(MvPolynomial (StageVars E) A) := Cardinal.mk_quotient_le
    _ ≤ #A ⊔ #(StageVars E) ⊔ ℵ₀ := MvPolynomial.cardinalMk_le_max
    _ ≤ κ := sup_le (sup_le hA (Cardinal.mk_le_aleph0.trans hκ)) hκ

/-- Counting representatives in a filtered colimit of commutative rings. -/
private theorem mk_colimit_le {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{max u v}) [HasColimit F] {κ : Cardinal.{max u v}}
    (hκ : ℵ₀ ≤ κ) (hJ : Cardinal.lift.{u} #J ≤ κ)
    (hF : ∀ j, #(F.obj j) ≤ κ) :
    #(colimit F : CommRingCat) ≤ κ := by
  letI : PreservesFilteredColimitsOfSize.{v, v} (forget CommRingCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink _
  have hs : Function.Surjective
      (fun x : Σ j, F.obj j ↦ (colimit.ι F x.1).hom x.2) := by
    intro x
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat) (colimit.isColimit F)) x
    exact ⟨⟨j, y⟩, hy⟩
  calc
    #(colimit F : CommRingCat) ≤ #(Σ j, F.obj j) :=
      Cardinal.mk_le_of_surjective hs
    _ = Cardinal.sum (fun j ↦ #(F.obj j)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : J ↦ κ) := Cardinal.sum_le_sum _ _ hF
    _ = Cardinal.lift.{u} #J * κ := by
      rw [Cardinal.sum_const, Cardinal.lift_id'.{v, u}, Cardinal.lift_umax.{v, u}]
    _ ≤ κ := Cardinal.mul_le_of_le hκ hJ le_rfl

/-- The ind-étale envelope has cardinality at most the maximum of the base
ring cardinality and the countable cardinal. -/
theorem mk_le_max (A : Type u) [CommRing A] :
    #(IndEtaleEnvelope A) ≤ #A ⊔ ℵ₀ := by
  letI : IsFiltered (Index A) :=
    { cocone_objs := fun E E' ↦
        ⟨⟨E.1 ∪ E'.1, E.2.union E'.2⟩,
          homOfLE Set.subset_union_left, homOfLE Set.subset_union_right, trivial⟩
      cocone_maps := fun {_ Y} _ _ ↦ ⟨Y, 𝟙 Y, Subsingleton.elim _ _⟩
      nonempty := ⟨emptyIndex A⟩ }
  refine mk_colimit_le (ringFunctor A) le_sup_right ?_ ?_
  · simpa using mk_index_le A le_sup_right le_sup_left
  · intro E
    exact mk_stage_le A le_sup_right le_sup_left E

/-- The ind-étale envelope has cardinality at most any infinite cardinal
bounding the base ring. -/
theorem mk_le (A : Type u) [CommRing A] {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (hA : #A ≤ κ) :
    #(IndEtaleEnvelope A) ≤ κ := by
  exact (mk_le_max A).trans (sup_le hA hκ)

/-- Every iterate of the ind-étale envelope has cardinality at most any
infinite cardinal bounding the base ring. -/
theorem mk_iterate_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) (n : ℕ) :
    #(iterate A n) ≤ κ := by
  induction n with
  | zero =>
      rw [iterate_zero]
      exact mk_le A hκ hA
  | succ n ih =>
      rw [iterate_succ]
      exact mk_le (iterate A n) hκ ih

/-- The sequential colimit of the iterated envelopes has cardinality at most
the maximum of the base ring cardinality and the countable cardinal. -/
theorem mk_iteration_le_max (A : Type u) [CommRing A] :
    #(Iteration A) ≤ #A ⊔ ℵ₀ := by
  refine mk_colimit_le (iterateFunctor A) le_sup_right ?_ ?_
  · simpa using (le_sup_right : ℵ₀ ≤ #A ⊔ ℵ₀)
  · intro n
    exact mk_iterate_le A le_sup_right le_sup_left n

/-- The sequential colimit of the iterated envelopes has cardinality at most
any infinite cardinal bounding the base ring. -/
theorem mk_iteration_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    #(Iteration A) ≤ κ := by
  exact (mk_iteration_le_max A).trans (sup_le hA hκ)

end Algebra.IndEtaleEnvelope
