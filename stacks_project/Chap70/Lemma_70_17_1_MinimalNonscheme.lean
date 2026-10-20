/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MinimalNonscheme

/-!
# Minimal nonscheme algebraic spaces

An algebraic space is a minimal nonscheme when it is not a scheme, but every
closed subspace whose inclusion is not an isomorphism is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.IsMinimalNonscheme :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isMinimalNonscheme_iff :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    IsMinimalNonscheme X ↔
      ¬ IsScheme X ∧ ∀ Z : ClosedSubspace X, ¬ IsIso Z.ι → IsScheme Z.X)

#check (AlgebraicGeometry.AlgebraicSpace.not_isScheme_of_isMinimalNonscheme :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, IsMinimalNonscheme X → ¬ IsScheme X)

#check (AlgebraicGeometry.AlgebraicSpace.isScheme_of_isMinimalNonscheme_of_not_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, IsMinimalNonscheme X →
    ∀ Z : ClosedSubspace X, ¬ IsIso Z.ι → IsScheme Z.X)

end AlgebraicGeometry.AlgebraicSpace
