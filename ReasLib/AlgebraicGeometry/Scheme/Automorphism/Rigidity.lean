/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Rigidity of scheme automorphisms

This file records rigidity properties of automorphisms of reduced finite-type schemes over fields
that act trivially on the underlying topological space.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SchemeOverField.Automorphism

variable {k : Type u} [Field k]

/-- An automorphism of a reduced finite-type scheme over a field is the identity if it fixes every
point and every irreducible component has positive topological Krull dimension. -/
theorem hom_eq_id_of_eqOnPoints_of_irreducibleComponents_posDim
    (X : SchemeOverField k) [IsReduced X.left] [Scheme.Hom.FiniteType X.hom]
    (f : X ≅ X) (h_points : ∀ x : X.left, f.hom.left x = x)
    (h_dim : ∀ Z : irreducibleComponents X.left, 0 < topologicalKrullDim Z) :
    f.hom = 𝟙 X := sorry

/-- Pulling back a coherent module along an automorphism of a reduced finite-type scheme over a
field that fixes every point gives an isomorphic module. -/
theorem pullback_isIsomorphic_of_isCoherent_of_eqOnPoints
    (X : SchemeOverField k) [IsReduced X.left] [Scheme.Hom.FiniteType X.hom]
    (f : X ≅ X) (h_points : ∀ x : X.left, f.hom.left x = x)
    (ℱ : X.left.Modules) [ℱ.IsCoherent] :
    CategoryTheory.IsIsomorphic ((Scheme.Modules.pullback f.hom.left).obj ℱ) ℱ := sorry

end AlgebraicGeometry.SchemeOverField.Automorphism
