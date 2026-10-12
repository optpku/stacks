/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
import StacksCheckRecall

@[expose] public section

universe u v

/-!
# Definition 34.4.1

This chapter entry identifies étale coverings with the families in the
canonical big étale precoverage and records their raw-family characterization.
-/

/- Definition 34.4.1: `Scheme.etalePrecoverage` is the canonical big étale
precoverage on schemes. -/
@[stacks 0215] #check (AlgebraicGeometry.Scheme.etalePrecoverage :
  CategoryTheory.Precoverage AlgebraicGeometry.Scheme.{u})

/- Membership of a family of arrows in the étale precoverage is equivalent to
joint surjectivity on points together with étaleness of every member. -/
#check (@AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff
    @AlgebraicGeometry.Etale :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    {X : ι → AlgebraicGeometry.Scheme.{u}} (f : ∀ i, X i ⟶ T),
      CategoryTheory.Presieve.ofArrows X f ∈
          AlgebraicGeometry.Scheme.etalePrecoverage T ↔
        ((∀ x : T, ∃ i, x ∈ Set.range (f i)) ∧
          ∀ i, AlgebraicGeometry.Etale (f i)))
