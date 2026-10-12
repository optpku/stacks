/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap86.«86_7_0_1_Comparison»
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 86.7.1 (1): let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
quasi-compact and quasi-separated algebraic spaces over `S`. Let `a` be a right
adjoint of `Rf_*` on `DerivedQCoh`. The comparison
`Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)` defined above for `K, L` in `DerivedQCoh Y` is an
isomorphism if `K` is perfect. -/
@[stacks 0E5Q]
theorem pullbackTensorRightAdjointMap_isIso_of_isPerfect
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) (hK : ModuleDerived.IsPerfect K.obj) :
    IsIso (pullbackTensorRightAdjointMap f a aAdjunction K L) :=
  sorry

/-- Lemma 86.7.1 (2): in particular, the specialization
`Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` of 86.7.0.1 is an isomorphism if `K` is perfect. -/
@[stacks 0E5Q]
theorem pullbackTensorDualityMap_isIso_of_isPerfect
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) (hK : ModuleDerived.IsPerfect K.obj) :
    IsIso (pullbackTensorDualityMap f a aAdjunction K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
