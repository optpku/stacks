module

public import ReasLib.RingTheory.LocalRing.Branches
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty.LocalRing

/-!
# Geometric branch properties of scheme germs

The property that a scheme stalk has a specified finite geometric branch number
is smooth local.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.GermProperty

/-- The germ property `P_n`: the stalk has geometric branch number `n`. -/
abbrev geometricBranchEq (n : ℕ) : GermProperty.{u} :=
  ofLocalRing (hasGeometricBranchNumber n)

/-- `geometricBranchEq n` is the stalkwise evaluation of
`hasGeometricBranchNumber n`. -/
theorem geometricBranchEq_apply (n : ℕ) (X : Scheme.{u}) (x : X) :
    geometricBranchEq n X x = hasGeometricBranchNumber n (X.presheaf.stalk x) :=
  sorry

/-- A scheme germ satisfies `geometricBranchEq n` if and only if the stalk has
geometric branch number `n`. -/
theorem geometricBranchEq_iff (n : ℕ) (X : Scheme.{u}) (x : X) :
    geometricBranchEq n X x ↔ hasGeometricBranchNumber n (X.presheaf.stalk x) :=
  sorry

/-- The germ property `geometricBranchEq n` is smooth local. -/
theorem geometricBranchEq_isSmoothLocal (n : ℕ) :
    (geometricBranchEq n).IsSmoothLocal :=
  sorry


end AlgebraicGeometry.GermProperty
