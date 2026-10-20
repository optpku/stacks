/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.FiniteRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

variable {T : Scheme.{u}} {ι : Type v}

/-- An indexed fppf-covering family of schemes is a `ph` covering family. -/
theorem AlgebraicGeometry.Scheme.FppfCovering.phCovering
    {family : ι → CategoryTheory.Over T}
    (hfamily : AlgebraicGeometry.Scheme.FppfCovering family) :
    AlgebraicGeometry.PhCovering (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := sorry

/-- A bundled fppf cover of a scheme is canonically a `ph` covering family. -/
theorem AlgebraicGeometry.FppfCover.phCovering
    {T : Scheme.{u}} (𝒰 : AlgebraicGeometry.FppfCover.{u, v} T) :
    AlgebraicGeometry.PhCovering 𝒰.X 𝒰.f := sorry
