/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The affine tilde adjunction

This leaf records the canonical adjunction between affine tilde sheaves and global sections.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.tilde

variable {R : CommRingCat.{u}} {M : ModuleCat R} {F : (Spec R).Modules}

/-- The canonical associated-module functor on `Spec R` is naturally isomorphic to affine tilde
sheafification. -/
@[stacks 01I7 "associated module versus affine tilde"]
noncomputable def associatedFunctorIso (R : CommRingCat.{u}) :
    RingedSpace.Module.Associated.functor (Scheme.ΓSpecIso R).inv.hom ≅
      tilde.functor R :=
  Adjunction.leftAdjointUniq
    ((@RingedSpace.Module.Associated.adjunction
      (Spec R).toLocallyRingedSpace.toRingedSpace R _
        (Scheme.ΓSpecIso R).inv.hom).ofNatIsoRight (Iso.refl _))
    (tilde.adjunction (R := R))

/-- The affine adjunction sends a sheaf morphism to its map on global sections precomposed with
the canonical affine comparison. -/
@[stacks 01I7, simp]
theorem adjunction_homEquiv_apply (f : tilde M ⟶ F) :
    tilde.adjunction.homEquiv M F f =
      (tilde.isoTop M).hom ≫ moduleSpecΓFunctor.map f := sorry

end AlgebraicGeometry.tilde
