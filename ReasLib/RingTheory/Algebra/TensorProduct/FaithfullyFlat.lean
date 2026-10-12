/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.LinearAlgebra.UniversallyInjective

/-!
# Faithful flatness from flat tensor-square coprojections

A universally injective algebra map with flat tensor-square coprojections is faithfully flat.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Module.FaithfullyFlat

/-- A commutative algebra is faithfully flat over its base ring if both coprojections into its
tensor square are flat and its structure map is universally injective. -/
theorem of_universallyInjective_of_coprojections_flat
    {B : Type u} {C : Type v} [CommRing B] [CommRing C] [Algebra B C]
    (h_includeLeft : (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] C).Flat)
    (h_includeRight : (Algebra.TensorProduct.includeRight : C →ₐ[B] C ⊗[B] C).toRingHom.Flat)
    (h_universallyInjective :
      LinearMap.UniversallyInjective.{u, u, v, max u v} (Algebra.linearMap B C)) :
    Module.FaithfullyFlat B C := sorry

end Module.FaithfullyFlat
