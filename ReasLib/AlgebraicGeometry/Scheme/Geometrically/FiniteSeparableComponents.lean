module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.Separable
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleComponent
import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.IrreducibleComponents.Descent

/-!
# Finite separable extensions and geometric irreducible components

This leaf gives the direct scheme-morphism form of the finite-separable
extension theorem for componentwise geometric irreducibility.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace GeometricallyIrreducible.Components

/-- A scheme locally of finite type over a field and with finitely many irreducible components
has geometrically irreducible canonical components after a finite separable field extension. -/
@[stacks 054R]
theorem existsFiniteSeparable
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    [Finite (irreducibleComponents X)] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
      all
        (FieldExtension.toBase k k' f) := sorry

end GeometricallyIrreducible.Components

end AlgebraicGeometry
