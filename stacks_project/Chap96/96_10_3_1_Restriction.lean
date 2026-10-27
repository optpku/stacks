/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SpaceRestriction

/-! # Restriction to the small étale site of a represented groupoid fibration -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
universe u

namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- The tautological functor from the small étale site of an algebraic space
to its represented groupoid fibration. -/
abbrev smallEtaleToGroupoids (F : AlgebraicSpace S) :
    smallEtaleSite F ⥤ F.toGroupoids.total :=
  GroupoidsOver.smallEtaleToGroupoids F

end AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.restrictEtale :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    Sheaf F.toGroupoids.etaleTopology (Type (u + 1)) ⥤
      Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type (u + 1)))

#check (AlgebraicGeometry.GroupoidsOver.smallEtaleToGroupoids_isContinuous :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    (AlgebraicGeometry.GroupoidsOver.smallEtaleToGroupoids F).IsContinuous
      (AlgebraicSpace.smallEtaleTopology F) F.toGroupoids.etaleTopology)
