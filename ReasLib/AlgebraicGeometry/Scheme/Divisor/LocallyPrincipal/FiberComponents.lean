module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Fiber

/-!
# Fiber components of locally principal closed subschemes

This file records when the support of a locally principal closed subscheme in a fiber is a union
of irreducible components.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a dominant locally finite-type morphism between irreducible schemes, the fiber support of
a locally principal closed subscheme avoiding the generic fiber is a union of irreducible
components when the special-fiber dimension is at most the generic-fiber dimension. -/
@[stacks 053R]
theorem fiberSupport_eq_iUnion_irreducibleComponents
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData) (s : S)
    [IrreducibleSpace S] [IrreducibleSpace X] [IsDominant f]
    [LocallyOfFiniteType f] [IsLocallyPrincipalClosedSubscheme Z.subschemeι]
    (hdim : topologicalKrullDim (f.fiber s) ≤
      topologicalKrullDim (f.fiber (genericPoint S)))
    (hη : Scheme.IdealSheafData.avoidsFiber f Z (genericPoint S)) :
    ∃ A : Set (irreducibleComponents (f.fiber s)),
      ((Z.comap (f.fiberι s)).support : Set (f.fiber s)) =
        ⋃ W ∈ A, (W : Set (f.fiber s)) := sorry

end AlgebraicGeometry.Scheme.Hom
