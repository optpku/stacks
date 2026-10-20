/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.LocallyQuasiFinite
import StacksCheckRecall

/-!
# Representability of separated locally quasi-finite algebraic spaces

A separated, locally quasi-finite morphism of algebraic spaces over a scheme
with representable target has representable source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/- Proposition 67.50.2: Let `S` be a scheme. Let `f : X ⟶ T` be a morphism of
algebraic spaces over `S`. If `T` is representable, `f` is locally quasi-finite,
and `f` is separated, then `X` is representable. -/
@[stacks 03XX] #check (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_locallyQuasiFinite_separated :
    ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T),
      [IsScheme T] → [LocallyOfFiniteType f] → [LocallyQuasiFinite f] →
      [Separated f] → IsScheme X)

end AlgebraicGeometry.AlgebraicSpace.IsScheme
