/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.Perfect
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 86.7.1 (1): let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
quasi-compact and quasi-separated algebraic spaces over `S`. Let `a` be a right
adjoint of `Rf_*` on `DerivedQCoh`. The comparison
`Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)` defined above for `K, L` in `DerivedQCoh Y` is an
isomorphism if `K` is perfect. -/
@[stacks 0E5Q]
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pullbackTensorRightAdjointMap_isIso_of_isPerfect :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y),
    ModuleDerived.IsPerfect K.obj → IsIso (pullbackTensorRightAdjointMap f a aAdjunction K L))

/- Lemma 86.7.1 (2): in particular, the specialization
`Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` of 86.7.0.1 is an isomorphism if `K` is perfect. -/
@[stacks 0E5Q]
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pullbackTensorDualityMap_isIso_of_isPerfect :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y),
    ModuleDerived.IsPerfect K.obj → IsIso (pullbackTensorDualityMap f a aAdjunction K))
