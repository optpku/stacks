module

public import Mathlib.Algebra.Field.Basic
public import stacks_project.Chap66.Lemma_66_25_4_Regular
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Lemma 72.16.1

An algebraic space smooth over a field is regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.16.1: let `k` be a field, and let `X` be an algebraic space smooth over `k`.
Then `X` is a regular algebraic space. -/
@[stacks 06M1]
instance isRegular_of_smooth_over_field {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Smooth (toBase X)] :
    IsRegular X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
