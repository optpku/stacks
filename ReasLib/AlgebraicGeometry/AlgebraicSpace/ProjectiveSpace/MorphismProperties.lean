/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace

/-- The structure morphism of projective space over an algebraic space is of finite
presentation. -/
instance instFinitePresentationToBase (n : ℕ) {S : Scheme.{u}}
    (B : AlgebraicSpace S) : FinitePresentation (toBase n B) := sorry

/-- The structure morphism of projective space over an algebraic space is separated. -/
instance instSeparatedToBase (n : ℕ) {S : Scheme.{u}}
    (B : AlgebraicSpace S) : Separated (toBase n B) := sorry

end AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace
