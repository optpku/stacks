module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The regular and singular loci of a scheme

The regular locus consists of the points whose local rings are regular local
rings. The singular locus is its complement. These definitions make sense for
every scheme.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The regular locus `Reg(X)` is the set of points `x` such that the stalk
`X.presheaf.stalk x` is a regular local ring. -/
@[stacks 07R1]
def regularLocus : Set X :=
  { x | IsRegularLocalRing (X.presheaf.stalk x) }

/- Regular-locus notation on schemes, attached to the owner
`AlgebraicGeometry.Scheme.regularLocus`. -/
scoped[AlgebraicGeometry] notation "Reg(" X ")" =>
  AlgebraicGeometry.Scheme.regularLocus X

/-- Membership in the regular locus means that the corresponding stalk is a regular local ring. -/
@[simp] theorem mem_regularLocus (x : X) :
    x ∈ Reg(X) ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
  Iff.rfl

/-- The singular locus `Sing(X)` is the complement of the regular locus. -/
@[stacks 07R1]
def singularLocus : Set X :=
  X.regularLocusᶜ

/- Singular-locus notation on schemes, attached to the owner
`AlgebraicGeometry.Scheme.singularLocus`. -/
scoped[AlgebraicGeometry] notation "Sing(" X ")" =>
  AlgebraicGeometry.Scheme.singularLocus X

/-- The singular locus is the complement of the regular locus. -/
theorem singularLocus_eq_compl_regularLocus :
    Sing(X) = Reg(X)ᶜ :=
  rfl

/-- The complement of the regular locus is the singular locus. -/
theorem compl_regularLocus_eq_singularLocus :
    Reg(X)ᶜ = Sing(X) :=
  rfl

/-- The regular locus is the complement of the singular locus. -/
theorem regularLocus_eq_compl_singularLocus :
    Reg(X) = Sing(X)ᶜ := by
  ext x
  simp [singularLocus]

/-- Membership in the singular locus means that the corresponding stalk is not a regular local
ring. -/
@[simp] theorem mem_singularLocus (x : X) :
    x ∈ Sing(X) ↔ ¬ IsRegularLocalRing (X.presheaf.stalk x) := by
  simp [AlgebraicGeometry.Scheme.singularLocus, AlgebraicGeometry.Scheme.regularLocus]

end AlgebraicGeometry.Scheme
