/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.UniversalHomeomorphism

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- A universal homeomorphism of universe-raised fppf sheaves over `Spec k`,
expressed by the general atlas criterion over the base scheme. -/
abbrev isUniversalHomeomorphism {k : Type u} [Field k]
    {X Y : Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1))}
    (f : X ⟶ Y) : Prop :=
  AlgebraicGeometry.AlgebraicSpace.Sheaf.isUniversalHomeomorphism f

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
