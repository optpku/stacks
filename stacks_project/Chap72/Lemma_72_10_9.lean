/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Locally quasi-finite algebraic spaces closed under monomorphisms over a field

A monomorphism of algebraic spaces over a field preserves the Stacks property of
being locally quasi-finite over that field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.10.9: Let `k` be a field. Let `f : X ⟶ Y` be a monomorphism of
algebraic spaces over `k`. If `Y` is locally quasi-finite over `k` so is `X`.

Stacks locally quasi-finite over `k` is `LocallyOfFiniteType (toBase X)` and
`LocallyQuasiFinite (toBase X)`. -/
@[stacks 06S1]
theorem locallyQuasiFinite_over_field_of_mono {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of k))} (f : X ⟶ Y) [Mono f]
    [LocallyOfFiniteType (toBase Y)] [LocallyQuasiFinite (toBase Y)] :
    LocallyOfFiniteType (toBase X) ∧ LocallyQuasiFinite (toBase X) :=
  sorry

/-- If `f : X ⟶ Y` is a monomorphism of algebraic spaces over a field `k` and
`Y` is locally quasi-finite over `k`, then `X` is locally of finite type over
`k`. -/
theorem locallyOfFiniteType_toBase_of_mono {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of k))} (f : X ⟶ Y) [Mono f]
    [LocallyOfFiniteType (toBase Y)] [LocallyQuasiFinite (toBase Y)] :
    LocallyOfFiniteType (toBase X) :=
  sorry

/-- If `f : X ⟶ Y` is a monomorphism of algebraic spaces over a field `k` and
`Y` is locally quasi-finite over `k`, then the structure morphism of `X` is
locally quasi-finite. -/
theorem locallyQuasiFinite_toBase_of_mono {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of k))} (f : X ⟶ Y) [Mono f]
    [LocallyOfFiniteType (toBase Y)] [LocallyQuasiFinite (toBase Y)] :
    LocallyQuasiFinite (toBase X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
