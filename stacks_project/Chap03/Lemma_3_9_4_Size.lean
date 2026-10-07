module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The Stacks size of a scheme, `ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(Γ(X, U))`. -/
noncomputable def size (X : Scheme.{u}) : Cardinal.{u} :=
  ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(Γ(X, U))

/-- Countable infinite cardinals are bounded by the Stacks size of any scheme. -/
lemma aleph0_le_size (X : Scheme.{u}) : ℵ₀ ≤ X.size := sorry

/-- The set of affine opens is bounded in cardinality by the Stacks size. -/
lemma cardinalMk_affineOpens_le_size (X : Scheme.{u}) : #X.affineOpens ≤ X.size := sorry

/-- Sections over an affine open are bounded in cardinality by the Stacks size. -/
lemma cardinalMk_sections_le_size (X : Scheme.{u}) (U : X.affineOpens) :
    #(Γ(X, U)) ≤ X.size := sorry

end AlgebraicGeometry.Scheme
