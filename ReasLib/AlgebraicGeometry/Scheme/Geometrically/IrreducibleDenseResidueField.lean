/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Closure

/-!
# Geometric irreducibility from dense residue-field points

This module gives a geometric-irreducibility criterion in terms of the density
of points whose residue-field maps are isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace GeometricallyIrreducible.ResidueField

section

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- An irreducible scheme over a field is geometrically irreducible when the points whose
residue-field maps are isomorphisms form a dense subset. -/
@[stacks 0G69]
theorem of_irreducibleSpace_of_denseIsIsoMap
    (hX : IrreducibleSpace X)
    (hdense : Dense ({x : X | IsIso (f.residueFieldMap x)} : Set X)) :
    GeometricallyIrreducible f := sorry

end

end GeometricallyIrreducible.ResidueField

end AlgebraicGeometry
