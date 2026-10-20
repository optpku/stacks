/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Types
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale

/-!
# Rig-étale completion maps

A locally of finite type morphism into a locally Noetherian algebraic space
that is étale over the complement of a closed subset induces a rig-étale
morphism of formal completions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally of finite type morphism into a locally Noetherian algebraic space
that is étale over the complement of a closed subset induces a rig-étale map
from the completion along its inverse image to the completion along that subset. -/
instance rigEtale_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X))
    [AlgebraicSpace.Etale (Open.complementComparison f T)] :
    FormalAlgebraicSpace.RigEtale (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
