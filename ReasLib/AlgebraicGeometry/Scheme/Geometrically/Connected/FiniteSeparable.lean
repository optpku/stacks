module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.AlgebraicGeometry.Over
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected
public import Mathlib.Tactic.CrossRefAttribute
import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.SeparableClosure
import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.CompactOpen
import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Closeds.Descent

/-!
# Finite-Separable Tests for Geometric Connectedness

Geometric connectedness is a property of a scheme morphism over a field, not
of a chosen affine presentation.  This leaf records the finite-separable test
at that level; affine spectra receive a thin bridge in the affine API.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.GeometricallyConnected

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A scheme over a field is geometrically connected exactly when all of its finite
separable field-extension base changes are connected. -/
@[stacks 0389]
theorem iff_finiteSeparable :
    GeometricallyConnected f ↔
        ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
        [Algebra.IsSeparable k K],
        ConnectedSpace
          (pullback f (Spec.map (ofHom (algebraMap k K))) : Scheme) := sorry

end AlgebraicGeometry.GeometricallyConnected
