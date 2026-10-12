/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.RatFunc.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Extension
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.FunctionField

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A morphism from the rational-function spectrum to a projective scheme over a field extends to
a morphism from the polynomial spectrum over the same field. -/
theorem exists_hom_fromPolynomial {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Projective sX]
    (φ : Spec (.of (RatFunc k)) ⟶ X)
    (hφ : φ ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc k)))) :
    ∃ ψ : Spec (.of (Polynomial k)) ⟶ X,
      ψ ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) ∧
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (RatFunc k))) ≫ ψ = φ :=
  sorry

/-- A morphism over a field from the function-field spectrum of the projective line to a
projective scheme extends to a morphism from the projective line over that field, whose
composition with the generic-point morphism is the original morphism. -/
theorem exists_hom_fromProjectiveLine {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Projective sX]
    (φ : Spec (ProjectiveLine.scheme k).functionField ⟶ X)
    (hφ : φ ≫ sX =
      (ProjectiveLine.scheme k).fromSpecStalk (genericPoint (ProjectiveLine.scheme k)) ≫
        ProjectiveLine.toSpec k) :
    ∃ ψ : ProjectiveLine.scheme k ⟶ X,
      ψ ≫ sX = ProjectiveLine.toSpec k ∧
        (ProjectiveLine.scheme k).fromSpecStalk (genericPoint (ProjectiveLine.scheme k)) ≫
          ψ = φ := sorry

end AlgebraicGeometry
