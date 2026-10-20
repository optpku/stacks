/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Radicial.UniversallyInjective
import StacksCheckRecall

/-!
# Universally injective morphisms of algebraic spaces that are radicial

A universally injective morphism of algebraic spaces over a scheme is radicial
as soon as it is decent, quasi-separated, or locally separated.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.3.4. A universally injective morphism of algebraic spaces over a scheme
is radicial if it is decent, quasi-separated, or locally separated. -/
@[stacks 0484]
#check (AlgebraicGeometry.AlgebraicSpace.Radicial.of_universallyInjective_of_decent :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [UniversallyInjective f] → [Decent f] → Radicial f)

#check (AlgebraicGeometry.AlgebraicSpace.Radicial.of_universallyInjective_of_quasiSeparated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [UniversallyInjective f] → [QuasiSeparated f] → Radicial f)

#check (AlgebraicGeometry.AlgebraicSpace.Radicial.of_universallyInjective_of_locallySeparated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [UniversallyInjective f] → [LocallySeparated f] → Radicial f)
