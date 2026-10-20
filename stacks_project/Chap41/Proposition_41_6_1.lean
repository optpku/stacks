/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Section
import StacksCheckRecall

open CategoryTheory

universe u

/- Proposition 41.6.1 (1): Any section of a separated morphism of schemes is a closed
immersion. -/
@[stacks 024T] #check
  (AlgebraicGeometry.Scheme.Hom.Section.isClosedImmersion :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X}
      [AlgebraicGeometry.IsSeparated f], s ≫ f = 𝟙 S →
        AlgebraicGeometry.IsClosedImmersion s)

/- Proposition 41.6.1 (2): Any section of an unramified morphism of schemes is an open
immersion. -/
@[stacks 024T] #check
  (AlgebraicGeometry.Scheme.Hom.Section.isOpenImmersion :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X}
      [AlgebraicGeometry.Unramified f], s ≫ f = 𝟙 S →
        AlgebraicGeometry.IsOpenImmersion s)

/- Proposition 41.6.1 (3): Any section of an unramified separated morphism of schemes is
both an open immersion and a closed immersion. -/
@[stacks 024T] #check
  (AlgebraicGeometry.Scheme.Hom.Section.isOpenImmersion_and_isClosedImmersion :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X}
      [AlgebraicGeometry.Unramified f] [AlgebraicGeometry.IsSeparated f],
        s ≫ f = 𝟙 S → AlgebraicGeometry.IsOpenImmersion s ∧
          AlgebraicGeometry.IsClosedImmersion s)
