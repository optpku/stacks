/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.SectionsWithSupport
import StacksCheckRecall

/-!
# Injectivity of sections with support along a closed immersion
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.9.1: sections of an injective abelian sheaf supported on a closed
subspace form an injective abelian sheaf on the closed subspace's small étale site. -/
@[stacks 0A4M] #check (AlgebraicGeometry.AlgebraicSpace.sectionsWithSupport_injective :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (ℐ : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) [Injective ℐ],
    Injective ((AlgebraicGeometry.AlgebraicSpace.sectionsWithSupport i).obj ℐ))

#check (AlgebraicGeometry.AlgebraicSpace.sectionsWithSupport_preservesInjectiveObjects :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    (AlgebraicGeometry.AlgebraicSpace.sectionsWithSupport i).PreservesInjectiveObjects)
