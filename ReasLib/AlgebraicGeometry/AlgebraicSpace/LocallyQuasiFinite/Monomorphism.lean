/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally of finite type monomorphism of algebraic spaces is locally quasi-finite. -/
instance locallyQuasiFinite_of_locallyOfFiniteType_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Mono f] : LocallyQuasiFinite f :=
  sorry

/-- A locally of finite type monomorphism of algebraic spaces is separated and locally
quasi-finite. -/
theorem separated_and_locallyQuasiFinite_of_locallyOfFiniteType_of_mono
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Mono f] : Separated f ∧ LocallyQuasiFinite f :=
  ⟨Separated.of_mono f, locallyQuasiFinite_of_locallyOfFiniteType_of_mono f⟩

end AlgebraicGeometry.AlgebraicSpace
