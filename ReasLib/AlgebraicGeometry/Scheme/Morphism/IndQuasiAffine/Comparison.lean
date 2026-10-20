/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.Composition

/-!
# Comparisons for ind-quasi-affine scheme morphisms

This file records standard implications from quasi-affineness and immersions
to ind-quasi-affineness.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.QuasiAffineHom

/-- Every quasi-affine scheme morphism is ind-quasi-affine. -/
theorem indQuasiAffineHom {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : QuasiAffineHom f) : IndQuasiAffineHom f := sorry

end AlgebraicGeometry.QuasiAffineHom

namespace AlgebraicGeometry.IsImmersion

/-- Every immersion of schemes is ind-quasi-affine. -/
theorem indQuasiAffineHom {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsImmersion f) : IndQuasiAffineHom f := sorry

end AlgebraicGeometry.IsImmersion
