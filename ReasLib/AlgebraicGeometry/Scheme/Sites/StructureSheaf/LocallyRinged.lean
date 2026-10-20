/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged

/-!
# Locally ringed structure sheaves on standard big scheme sites
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The lifted global-functions sheaf on every standard big scheme site is locally ringed. -/
instance bigCommStructureSheafIsLocallyRinged (τ : StandardTopology) (X : Scheme.{u}) :
    (bigCommStructureSheaf τ X).IsLocallyRinged := sorry

/-- The commutative structure sheaf on the small étale site of a scheme is locally ringed. -/
instance smallCommStructureSheaf_etale_isLocallyRinged (S : Scheme.{u}) :
    (smallCommStructureSheaf .etale S).IsLocallyRinged := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
