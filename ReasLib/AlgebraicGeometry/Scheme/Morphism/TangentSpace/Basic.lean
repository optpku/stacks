/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative tangent spaces of scheme morphisms

This leaf owns the derivation model of the tangent space of a scheme morphism
at a point and its canonical residue-field module structure.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

noncomputable section

/-- The relative tangent space of `f : X ⟶ Y` at `x`, modeled as derivations
`Der_{𝒪_{Y, f(x)}}(𝒪_{X, x}, κ(x))`. -/
@[stacks 0BEA]
abbrev relativeTangentSpaceAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Type _ :=
  -- Local declaration justification (defeq pin): use the stalk map's canonical algebra
  -- so the source derivation module is definitionally the one attached to `f`.
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  -- Local declaration justification (defeq pin): use the residue morphism's canonical algebra
  -- so derivation values carry the residue-field module structure at `x`.
  let _ : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  -- Local declaration justification (defeq pin): use the composite stalk-to-residue algebra
  -- required by the relative derivation type over the base stalk.
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.residueField x) :=
    ((X.residue x).hom.comp (f.stalkMap x).hom).toAlgebra
  Derivation (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) (X.residueField x)

/-- For a morphism `f : X ⟶ S` and a point `x : X`, `tangentSpaceAt f x` is the
canonical `κ(x)`-vector space of relative tangent vectors. -/
@[stacks 0B2C]
abbrev tangentSpaceAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Type _ :=
  relativeTangentSpaceAt f x

/-- The tangent space `tangentSpaceAt f x` is definitionally equal to the relative tangent space
`relativeTangentSpaceAt f x`. -/
@[stacks 0B2C]
theorem tangentSpaceAt_def {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    tangentSpaceAt f x = relativeTangentSpaceAt f x := sorry

/-- The tangent space `tangentSpaceAt f x` carries the canonical `κ(x)`-module structure
inherited from derivations. -/
@[instance]
instance tangentSpaceAtModule {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Module (X.residueField x) (tangentSpaceAt f x) :=
  inferInstance

end

end AlgebraicGeometry.Scheme.Hom
