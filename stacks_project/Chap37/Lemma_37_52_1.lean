module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal.FiberComponents

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.52.1: for a dominant locally finite-type morphism between irreducible schemes,
the support of a locally principal closed subscheme in a fibre is a union of irreducible
components when it avoids the generic fibre and the special-fibre dimension is at most the
generic-fibre dimension. -/
@[stacks 053R] #check
  (AlgebraicGeometry.Scheme.Hom.fiberSupport_eq_iUnion_irreducibleComponents :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData) (s : S)
    [IrreducibleSpace S] [IrreducibleSpace X] [IsDominant f]
    [LocallyOfFiniteType f] [IsLocallyPrincipalClosedSubscheme Z.subschemeι]
    (hdim : topologicalKrullDim (f.fiber s) ≤
      topologicalKrullDim (f.fiber (genericPoint S)))
    (hη : Scheme.IdealSheafData.avoidsFiber f Z (genericPoint S)),
    ∃ A : Set (irreducibleComponents (f.fiber s)),
      ((Z.comap (f.fiberι s)).support : Set (f.fiber s)) =
        ⋃ W ∈ A, (W : Set (f.fiber s)))
