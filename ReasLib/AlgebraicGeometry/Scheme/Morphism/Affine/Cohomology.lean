/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCriterion

/-!
# An affine criterion from vanishing of a higher direct image

A quasi-compact morphism between quasi-separated schemes is affine when its first higher direct
image vanishes on every quasi-coherent ideal subobject of the source structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact morphism between quasi-separated schemes is affine if its first higher direct
image vanishes on every quasi-coherent ideal subobject of the source structure sheaf. -/
theorem isAffineHom_of_R1_pushforward_vanishes_for_quasiCoherent_idealSheaves
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparatedSpace X.carrier] [QuasiSeparatedSpace Y.carrier]
    [HasInjectiveResolutions X.Modules]
    (hR1 : ∀ I : Scheme.IdealSubobject X, I.toModule.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj I.toModule)) :
    IsAffineHom f := sorry

end AlgebraicGeometry.Scheme
