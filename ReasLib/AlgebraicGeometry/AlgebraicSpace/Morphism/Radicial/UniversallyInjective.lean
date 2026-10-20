/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Radicial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective.Characterization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Radicial and universally injective morphisms of algebraic spaces

A radicial morphism of algebraic spaces over a scheme is universally injective.
Conversely, a universally injective morphism is radicial as soon as it is decent,
quasi-separated, or locally separated.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Radicial

/-- A radicial morphism of algebraic spaces is injective on field-valued points. -/
theorem injectiveOnFieldPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Radicial f] : AlgebraicSpace.injectiveOnFieldPoints f :=
  sorry

/-- A radicial morphism of algebraic spaces over a scheme is universally injective. -/
instance universallyInjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Radicial f] : UniversallyInjective f :=
  (AlgebraicGeometry.AlgebraicSpace.UniversallyInjective.iff_injectiveOnFieldPoints f).mpr
    Radicial.injectiveOnFieldPoints

/-- A universally injective decent morphism of algebraic spaces over a scheme
is radicial. -/
instance of_universallyInjective_of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [UniversallyInjective f] [Decent f] : Radicial f :=
  sorry

/-- A universally injective quasi-separated morphism of algebraic spaces over a
scheme is radicial. -/
instance of_universallyInjective_of_quasiSeparated {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [UniversallyInjective f] [QuasiSeparated f] :
    Radicial f :=
  sorry

/-- A universally injective locally separated morphism of algebraic spaces over a
scheme is radicial. -/
instance of_universallyInjective_of_locallySeparated {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [UniversallyInjective f] [LocallySeparated f] :
    Radicial f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Radicial
