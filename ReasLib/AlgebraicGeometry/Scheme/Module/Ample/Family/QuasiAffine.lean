/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Ample

/-!
# Ample families and quasi-affine morphisms

This file records preservation of the existence of ample families under quasi-affine and
affine morphisms of schemes.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.Modules.AmpleFamily

/-- A quasi-affine morphism of schemes transfers the existence of an ample family of
invertible modules from its target to its source. -/
theorem exists_of_quasiAffineHom {X Y : Scheme.{u}} {ι : Type v}
    (f : X ⟶ Y) (M : ι → Y.Modules) (hM : AmpleFamily M) (hf : QuasiAffineHom f) :
    ∃ (κ : Type (max u v)) (N : κ → X.Modules), AmpleFamily N := sorry

/-- An affine morphism of schemes transfers the existence of an ample family of
invertible modules from its target to its source. -/
theorem exists_of_isAffineHom {X Y : Scheme.{u}} {ι : Type v}
    (f : X ⟶ Y) [IsAffineHom f] (M : ι → Y.Modules) (hM : AmpleFamily M) :
    ∃ (κ : Type (max u v)) (N : κ → X.Modules), AmpleFamily N := sorry

end AlgebraicGeometry.Scheme.Modules.AmpleFamily
