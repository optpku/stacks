/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap93.Situation_93_9_9_Cover
public import stacks_project.Chap93.Situation_93_9_9_Deformation

/-!
# Glueing situation for deformation categories of schemes

Two affine opens with affine overlap, together with the named deformation
categories of the scheme, the opens, and the section rings.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/-- Situation 93.9.9
Let `Λ → k` be as in Section 93.3. Let `X` be a scheme over `k` which has an
affine open covering `X = U₁ ∪ U₂` with `U₁₂ = U₁ ⊓ U₂` affine too. Write
`U₁ = Spec(P₁)`, `U₂ = Spec(P₂)` and `U₁₂ = Spec(P₁₂)`, realizing `P₁ = Γ(X, U₁)`,
`P₂ = Γ(X, U₂)` and `P₁₂ = Γ(X, U₁ ⊓ U₂)`. Let
`TwoAffineOpenCover.deformationCategory`,
`TwoAffineOpenCover.deformationCategory_U₁`,
`TwoAffineOpenCover.deformationCategory_U₂`, and
`TwoAffineOpenCover.deformationCategory_inf` be as in Example 93.9.1 and let
`TwoAffineOpenCover.deformationCategory_ring₁`,
`TwoAffineOpenCover.deformationCategory_ring₂`, and
`TwoAffineOpenCover.deformationCategory_ringInf` be as in
Example 93.8.1. -/
@[stacks 0DYY]
abbrev TwoAffineOpenCover := Scheme.TwoAffineOpenCover

/-- The two affine opens are affine, their overlap is affine, and they cover `X`. -/
theorem TwoAffineOpenCover.spec {X : Scheme.{u}} (c : TwoAffineOpenCover X) :
    IsAffineOpen c.U₁ ∧ IsAffineOpen c.U₂ ∧ IsAffineOpen (c.U₁ ⊓ c.U₂) ∧ c.U₁ ⊔ c.U₂ = ⊤ :=
  sorry
