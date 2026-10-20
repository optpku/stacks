/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic

/-!
# Smooth locality on source-and-target for standard morphism properties

Flat, locally of finite presentation, locally of finite type, universally open,
syntomic, and smooth morphisms of algebraic spaces are smooth local on the
source-and-target.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Flat

/-- Flatness of morphisms of algebraic spaces is smooth local on the
source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget (@Flat S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Flat

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation

/-- Local finite presentation of morphisms of algebraic spaces is smooth local
on the source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType

/-- Local finite type of morphisms of algebraic spaces is smooth local on the
source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType

namespace AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-- Universal openness of morphisms of algebraic spaces is smooth local on the
source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget
      (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

namespace AlgebraicGeometry.AlgebraicSpace.Syntomic

/-- Syntomicity of morphisms of algebraic spaces is smooth local on the
source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget
      (@Syntomic S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Syntomic

namespace AlgebraicGeometry.AlgebraicSpace.Smooth

/-- Smoothness of morphisms of algebraic spaces is smooth local on the
source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget
      (@Smooth S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Smooth
