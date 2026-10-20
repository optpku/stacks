/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- A derived module on a scheme is perfect if and only if all its pullbacks
along an fpqc covering family are perfect. -/
theorem isPerfect_iff_fpqcCovering {X : Scheme.{u}} {ι : Type v}
    (family : ι → Over X) (hfamily : Scheme.FpqcCovering family)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    RingedSpace.ModuleDerived.IsPerfect E ↔
      ∀ i : ι, RingedSpace.ModuleDerived.IsPerfect
        ((RingedSpace.modulePullbackDerived (family i).hom.toLRSHom.toShHom).obj E) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
