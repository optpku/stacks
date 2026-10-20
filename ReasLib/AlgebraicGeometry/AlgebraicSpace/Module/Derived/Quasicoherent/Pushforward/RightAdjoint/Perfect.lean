/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.ProjectionFormula
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence

/-! # Perfect objects and the right-adjoint tensor comparison -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a morphism between quasi-compact and quasi-separated algebraic spaces, the
canonical comparison `Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)` for a right adjoint `a` of
derived pushforward is an isomorphism when `K` is perfect. -/
theorem pullbackTensorRightAdjointMap_isIso_of_isPerfect
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) (hK : ModuleDerived.IsPerfect K.obj) :
    IsIso (pullbackTensorRightAdjointMap f a aAdjunction K L) :=
  sorry

/-- For a morphism between quasi-compact and quasi-separated algebraic spaces, the
canonical structure-sheaf comparison `Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` is an isomorphism
when `K` is perfect. -/
theorem pullbackTensorDualityMap_isIso_of_isPerfect
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) (hK : ModuleDerived.IsPerfect K.obj) :
    IsIso (pullbackTensorDualityMap f a aAdjunction K) :=
  sorry

/-- Perfectness of `K`, supplied as a fact, makes the canonical right-adjoint tensor
comparison an isomorphism for morphisms between quasi-compact and quasi-separated
algebraic spaces. -/
instance isIso_pullbackTensorRightAdjointMap_of_isPerfect
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K L : DerivedQCoh Y) [hK : Fact (ModuleDerived.IsPerfect K.obj)] :
    IsIso (pullbackTensorRightAdjointMap f a aAdjunction K L) :=
  pullbackTensorRightAdjointMap_isIso_of_isPerfect f a aAdjunction K L hK.out

/-- Perfectness of `K`, supplied as a fact, makes the canonical structure-sheaf
duality comparison an isomorphism for morphisms between quasi-compact and
quasi-separated algebraic spaces. -/
instance isIso_pullbackTensorDualityMap_of_isPerfect
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) [hK : Fact (ModuleDerived.IsPerfect K.obj)] :
    IsIso (pullbackTensorDualityMap f a aAdjunction K) :=
  pullbackTensorDualityMap_isIso_of_isPerfect f a aAdjunction K hK.out

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
