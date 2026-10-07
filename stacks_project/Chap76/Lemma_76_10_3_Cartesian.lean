module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import stacks_project.Chap76.Definition_76_9_1_Arrow

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
