/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Arrow

/-!
# Cartesian morphisms of thickenings of algebraic spaces

If a morphism of thickenings of algebraic spaces over a scheme is cartesian
and both horizontal maps are locally of finite type, then the listed morphism
properties hold for the closed map if and only if they hold for the ambient
map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening.Hom

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is locally quasi-finite if and only if the ambient
map is locally quasi-finite. -/
theorem locallyQuasiFinite_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    LocallyQuasiFinite g.left ↔ LocallyQuasiFinite g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is finite if and only if the ambient map is finite. -/
theorem isFinite_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsFinite g.left ↔ IsFinite g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is a closed immersion if and only if the ambient
map is a closed immersion. -/
theorem isClosedImmersion_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsClosedImmersion g.left ↔ IsClosedImmersion g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the relative differentials of the closed map vanish if and only if
those of the ambient map vanish. -/
theorem isZero_relativeDifferentials_iff {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsZero (Ω[g.left]) ↔ IsZero (Ω[g.right]) := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is unramified if and only if the ambient map is
unramified. -/
theorem unramified_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Unramified g.left ↔ Unramified g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is a monomorphism if and only if the ambient map is
a monomorphism. -/
theorem mono_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Mono g.left ↔ Mono g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is an immersion if and only if the ambient map is an
immersion. -/
theorem isImmersion_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsImmersion g.left ↔ IsImmersion g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is proper if and only if the ambient map is proper. -/
theorem proper_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Proper g.left ↔ Proper g.right := sorry

end AlgebraicGeometry.AlgebraicSpace.Thickening.Hom
