/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.PullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.PullbackSections

/-- Pullback sections of a quasi-coherent module form a sheaf for the fpqc topology on
schemes over the base. -/
theorem isSheaf_fpqc (S : Scheme.{u}) (ℱ : S.Modules) [ℱ.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (over S ℱ) := sorry

/-- Pullback sections of a quasi-coherent module form a sheaf for each of the five standard
topologies on schemes over the base. -/
theorem isSheaf_standard (τ : StandardTopology) (S : Scheme.{u})
    (ℱ : S.Modules) [ℱ.IsQuasicoherent] :
    Presheaf.IsSheaf (τ.overTopology S) (over S ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.PullbackSections
