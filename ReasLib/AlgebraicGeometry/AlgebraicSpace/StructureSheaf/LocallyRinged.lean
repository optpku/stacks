/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.CommRing
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
public import Mathlib.CategoryTheory.Sites.LeftExact

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The universe-lifted structure sheaf on the small étale site of an algebraic space is locally
ringed. -/
instance commStructureSheafLift_isLocallyRinged {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (commStructureSheafLift X).IsLocallyRinged := sorry

end AlgebraicGeometry.AlgebraicSpace
