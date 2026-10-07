module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_4_6_Topology

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 110.51.1: there exists an étale morphism of algebraic spaces `f : X ⟶ Y`
and a nontrivial specialization of points `x ⤳ x'` in `|X|` with `f(x) = f(x')`
in `|Y|`. -/
@[stacks 06UK]
theorem exists_etale_nontrivial_specialization_in_fibre :
    ∃ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y) (x x' : Points X),
      Etale f ∧ Specializes x x' ∧ x ≠ x' ∧ Points.map f x = Points.map f x' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
