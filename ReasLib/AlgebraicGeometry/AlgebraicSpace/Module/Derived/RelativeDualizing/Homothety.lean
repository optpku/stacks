module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom.Homothety
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Cohomology.Basic

/-! # Homothety and cohomology of relative dualizing complexes -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

/-- For a proper, flat, finitely presented morphism of algebraic spaces, the canonical
scalar homothety of a relative dualizing complex is an isomorphism. -/
theorem homothety_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f] (C : RelativeDualizingComplex f) :
    IsIso (ModuleDerived.InternalHom.homothety C.complex) := sorry

/-- For a proper, flat, finitely presented morphism of algebraic spaces, the derived
pushforward of a relative dualizing complex has zero cohomology sheaves in positive degrees. -/
theorem pushforward_cohomology_isZero_of_pos {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f] (C : RelativeDualizingComplex f)
    (i : ℤ) (hi : 0 < i) :
    IsZero (ModuleDerived.cohomologySheaf
      ((Modules.moduleDerivedPushforward f).obj C.complex) i) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
