/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage

/-!
# Closed-immersion pushforward of injective abelian sheaves

The small étale abelian direct image along a closed immersion of algebraic spaces
preserves injective objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The small étale abelian direct image along a closed immersion of algebraic spaces
preserves injective objects. -/
instance sheafPushforward_preservesInjectiveObjects_of_isClosedImmersion
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    (sheafPushforward AddCommGrpCat.{u + 1} i).PreservesInjectiveObjects := sorry

end AlgebraicGeometry.AlgebraicSpace
