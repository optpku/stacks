/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally projective module sheaves on schemes

Local projectivity of a scheme module is modeled by projectivity of its sections over every
affine open.  This is a scheme-specific property: its definition intrinsically refers to affine
open subschemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A scheme module is locally projective when its sections over every affine open are
projective modules over the corresponding ring of functions. -/
@[stacks 05JP]
class IsLocallyProjective (ℱ : X.Modules) : Prop where
  /-- Projectivity of the sections over a chosen affine open. -/
  affineOpen_projective (U : X.affineOpens) :
    Module.Projective Γ(X, U) Γ(ℱ, U)

/-- A locally projective module has projective sections over every affine open. -/
theorem IsLocallyProjective.projective_sections
    (ℱ : X.Modules) [IsLocallyProjective ℱ]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Projective Γ(X, U) Γ(ℱ, U) := sorry

/-- A locally projective module has projective sections on an affine open packaged in
`X.affineOpens`. -/
theorem IsLocallyProjective.projective_sections_affineOpen
    (ℱ : X.Modules) [hℱ : IsLocallyProjective ℱ]
    (U : X.affineOpens) :
    Module.Projective Γ(X, U) Γ(ℱ, U) := sorry

/-- Projectivity of sections over an affine open is available to typeclass search from local
projectivity. -/
instance instProjectiveSectionsOfIsLocallyProjective
    (ℱ : X.Modules) [IsLocallyProjective ℱ]
    (U : X.Opens) [Fact (IsAffineOpen U)] :
    Module.Projective Γ(X, U) Γ(ℱ, U) := sorry

/-- Local projectivity is equivalent to affine-open sectionwise projectivity. -/
theorem isLocallyProjective_iff
    (ℱ : X.Modules) :
    IsLocallyProjective ℱ ↔
      ∀ U : X.Opens, IsAffineOpen U → Module.Projective Γ(X, U) Γ(ℱ, U) := sorry

end AlgebraicGeometry.Scheme.Modules
