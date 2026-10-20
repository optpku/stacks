/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.TwoAffineOpenCover
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.TwoAffineOpenCover

/-!
# Glueing situation for deformation categories of schemes

Two affine opens with affine overlap, together with the named deformation
categories of the scheme, the opens, and the section rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Situation 93.9.9
Let `Λ → k` be as in Section 93.3. Let `X` be a scheme over `k` which has an
affine open covering `X = U₁ ∪ U₂` with `U₁₂ = U₁ ⊓ U₂` affine too. Write
`U₁ = Spec(P₁)`, `U₂ = Spec(P₂)` and `U₁₂ = Spec(P₁₂)`, realizing `P₁ = Γ(X, U₁)`,
`P₂ = Γ(X, U₂)` and `P₁₂ = Γ(X, U₁ ⊓ U₂)`. Let
`FlatSchemeCat.deformationCategory`,
`TwoAffineOpenCover.deformationCategory_U₁`,
`TwoAffineOpenCover.deformationCategory_U₂`, and
`TwoAffineOpenCover.deformationCategory_inf` be as in Example 93.9.1 and let
`TwoAffineOpenCover.deformationCategory_ring₁`,
`TwoAffineOpenCover.deformationCategory_ring₂`, and
`TwoAffineOpenCover.deformationCategory_ringInf` be as in
Example 93.8.1. -/
@[stacks 0DYY] #check (AlgebraicGeometry.Scheme.TwoAffineOpenCover : Scheme.{u} → Type u)

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X : Scheme.{u}} (c : TwoAffineOpenCover X)
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))

-- The deformation category of X.
#check (FlatSchemeCat.deformationCategory Λ k X hX : Type (u + 1))

-- The deformation categories of U₁, U₂, and U₁₂.
#check (deformationCategory_U₁ Λ k c hX : Type (u + 1))
#check (deformationCategory_U₂ Λ k c hX : Type (u + 1))
#check (deformationCategory_inf Λ k c hX : Type (u + 1))

-- The deformation categories of P₁, P₂, and P₁₂.
#check (deformationCategory_ring₁ Λ k c hX : Type (u + 1))
#check (deformationCategory_ring₂ Λ k c hX : Type (u + 1))
#check (deformationCategory_ringInf Λ k c hX : Type (u + 1))

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
