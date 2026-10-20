module

public import Mathlib.SetTheory.Ordinal.Basic
public import ReasLib.Algebra.Homology.CochainComplex.WellOrderedLimit
import StacksCheckRecall

/-!
# Lemma 12.31.8

The reusable theorem is indexed by an arbitrary well-ordered type.  This source facade records
its ordinal specialization and the bridge from underlying surjectivity to categorical
epimorphisms in `AddCommGrpCat`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

/- Lemma 12.31.8: if an inverse system of acyclic cochain complexes of abelian groups indexed by
the ordinals below `α` has surjective canonical maps from every stage to the inverse limit over
its strict predecessors in every degree, then its inverse limit is acyclic. -/
@[stacks 0AAT]
#check
  (fun {α : Ordinal.{u}}
      (K : α.ToTypeᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)
      (hacyclic : ∀ β : α.ToType, (K.obj (op β)).Acyclic)
      (hsurjective : ∀ (β : α.ToType) (n : ℤ),
        Function.Surjective (((K.predecessorLimitComparison β).f n).hom)) ↦
    CochainComplex.limitAcyclic_of_predecessorComparison_epi K hacyclic
      (fun β ↦
        HomologicalComplex.epi_of_epi_f (K.predecessorLimitComparison β)
          (fun n ↦
            (AddCommGrpCat.epi_iff_surjective
              ((K.predecessorLimitComparison β).f n)).2 (hsurjective β n))))

/- The stage transition maps form a canonical cone before any predecessor limit is chosen. -/
#check CategoryTheory.Functor.predecessorCone

/- The source's comparison morphism is the category-general predecessor-limit comparison. -/
#check CategoryTheory.Functor.predecessorLimitComparison

/- Its projection formula recovers every transition map from the current stage. -/
#check CategoryTheory.Functor.predecessorLimitComparison.π

/- Its full universal specification is available without unfolding the comparison. -/
#check CategoryTheory.Functor.predecessorLimitComparison.existsUnique
