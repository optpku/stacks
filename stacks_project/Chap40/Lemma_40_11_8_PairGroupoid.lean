/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pair

/-!
# Pair groupoids of schemes

Compatibility bridge for the pair groupoid and the canonical morphism to it.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

#check
  (AlgebraicGeometry.GroupoidScheme.pair :
    {S : Scheme.{u}} → Over S → AlgebraicGeometry.GroupoidScheme S)

#check
  (AlgebraicGeometry.GroupoidScheme.toPair :
    {S : Scheme.{u}} → (G : AlgebraicGeometry.GroupoidScheme S) →
      AlgebraicGeometry.GroupoidScheme.Hom G (AlgebraicGeometry.GroupoidScheme.pair G.U))

end AlgebraicGeometry.GroupoidScheme
