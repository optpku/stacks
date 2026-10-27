/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect

/-! # Derived structure-sheaf duals on algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The derived dual is derived sheaf Hom into the structure sheaf concentrated in degree zero. -/
def dual (P : ModuleDerived X) : ModuleDerived X :=
  InternalHom.obj P ((DerivedCategory.singleFunctor (Modules X) 0).obj (𝟙_ (Modules X)))

/-- A source representative and a K-injective representative of the degree-zero structure
sheaf compute the derived dual, independently of the chosen representatives. -/
theorem dual_model (P : ModuleDerived X) (F I : CochainComplex (Modules X) ℤ)
    [I.IsKInjective] (sourceIso : DerivedCategory.Q.obj F ≅ P)
    (targetIso : DerivedCategory.Q.obj I ≅
      (DerivedCategory.singleFunctor (Modules X) 0).obj (𝟙_ (Modules X))) :
    IsIsomorphic (dual P) (DerivedCategory.Q.obj (InternalHom.complex F I)) := sorry

/-- The derived structure-sheaf dual of a perfect derived module is perfect. -/
theorem isPerfect_dual (E : ModuleDerived X) (hE : IsPerfect E) :
    IsPerfect (dual E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
