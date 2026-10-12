/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Morphisms.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Thickening.Hom

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is locally quasi-finite if and only if the ambient map is locally quasi-finite. -/
theorem locallyQuasiFinite_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    LocallyQuasiFinite g.left ↔ LocallyQuasiFinite g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is finite if and only if the ambient map is finite. -/
theorem isFinite_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsFinite g.left ↔ IsFinite g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is a closed immersion if and only if the ambient map is a closed immersion. -/
theorem isClosedImmersion_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsClosedImmersion g.left ↔ IsClosedImmersion g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the relative differentials of the closed map vanish if and only if those of the ambient map
vanish. -/
theorem isZero_relativeDifferentials_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Limits.IsZero (Ω[g.left.toShHom]) ↔ Limits.IsZero (Ω[g.right.toShHom]) := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is unramified if and only if the ambient map is unramified. -/
theorem unramified_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Unramified g.left ↔ Unramified g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is a monomorphism if and only if the ambient map is a monomorphism. -/
theorem mono_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Mono g.left ↔ Mono g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is an immersion if and only if the ambient map is an immersion. -/
theorem isImmersion_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsImmersion g.left ↔ IsImmersion g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is proper if and only if the ambient map is proper. -/
theorem isProper_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsProper g.left ↔ IsProper g.right := sorry

end AlgebraicGeometry.Thickening.Hom
