/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Locally quasi-finite morphisms of algebraic spaces and relative dimension zero

A locally finite-type morphism of algebraic spaces is locally quasi-finite
exactly when it has relative dimension zero at every source point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.34.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type. Then `f` is
locally quasi-finite if and only if `f` has relative dimension `0` at each
point of `|X|`. -/
@[stacks 04NV]
theorem locallyQuasiFinite_iff_relativeDimension_zero {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyQuasiFinite f ↔ RelativeDimension f 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
