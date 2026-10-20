module

public import Mathlib.Data.ENat.Lattice
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty.GeometricBranch
public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricBranch
public import ReasLib.AlgebraicGeometry.AlgebraicStack.GermProperty

/-!
# Geometric branch numbers of algebraic stacks at a point

The geometric branch number at a point is the unique finite branch number
witnessed by a smooth scheme chart through that point, or infinity when no
finite branch number is witnessed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack `X` has geometric branch number `n` at `x` if some
smooth scheme chart through `x` has stalkwise geometric branch number `n` at
the source point. -/
def hasGeometricBranchNumberAt {S : Scheme.{u}} (n : ℕ) (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  existsSmoothAt (GermProperty.geometricBranchEq n) X x

/-- `hasGeometricBranchNumberAt n X x` is the existence of a smooth scheme chart
through `x` on which the source has geometric branch number `n`. -/
theorem hasGeometricBranchNumberAt_def {S : Scheme.{u}} (n : ℕ)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    hasGeometricBranchNumberAt n X x ↔
      hasSmoothLocalAt (GermProperty.geometricBranchEq n)
        (GermProperty.geometricBranchEq_isSmoothLocal n) X x :=
  sorry

namespace hasGeometricBranchNumberAt

/-- A smooth morphism from a scheme through `x` on which the source has
geometric branch number `n` witnesses `hasGeometricBranchNumberAt n X x`. -/
theorem of {S : Scheme.{u}} {n : ℕ} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} {U : Over S} (p : GroupoidsOver.slice U ⟶ X) (u : U.left)
    [Groupoids.Hom.Smooth p] (hx : Points.mapSlice p u = x)
    (hPu : GermProperty.geometricBranchEq n U.left u) :
    hasGeometricBranchNumberAt n X x :=
  sorry

/-- An algebraic stack satisfying `hasGeometricBranchNumberAt n X x` admits a
smooth scheme chart through `x` on which the source has geometric branch number
`n`. -/
theorem spec {S : Scheme.{u}} {n : ℕ} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : hasGeometricBranchNumberAt n X x) :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
      Groupoids.Hom.Smooth p ∧ Points.mapSlice p u = x ∧
        GermProperty.geometricBranchEq n U.left u :=
  sorry

/-- At most one natural number is the geometric branch number of `X` at `x`. -/
theorem unique {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} {n m : ℕ} (hn : hasGeometricBranchNumberAt n X x)
    (hm : hasGeometricBranchNumberAt m X x) : n = m :=
  sorry

end hasGeometricBranchNumberAt

/-- `hasGeometricBranchNumberAt n X x` if and only if every smooth scheme chart
through `x` has geometric branch number `n` at the source point. -/
theorem hasGeometricBranchNumberAt_iff_forallSmoothAt {S : Scheme.{u}} (n : ℕ)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    hasGeometricBranchNumberAt n X x ↔
      forallSmoothAt (GermProperty.geometricBranchEq n) X x :=
  sorry

/-- `hasGeometricBranchNumberAt n X x` if and only if some smooth scheme chart
through `x` has geometric branch number `n` at the source point. -/
theorem hasGeometricBranchNumberAt_iff_existsSmoothAt {S : Scheme.{u}} (n : ℕ)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    hasGeometricBranchNumberAt n X x ↔
      existsSmoothAt (GermProperty.geometricBranchEq n) X x :=
  sorry

/-- `hasGeometricBranchNumberAt n X x` if and only if some smooth algebraic-space
chart through `x` has geometric branch number `n` at the source point. -/
theorem hasGeometricBranchNumberAt_iff_existsSmoothSpaceAt {S : Scheme.{u}}
    (n : ℕ) (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    hasGeometricBranchNumberAt n X x ↔
      existsSmoothSpaceAt (GermProperty.geometricBranchEq n) X x :=
  sorry

/-- On a scheme slice, `hasGeometricBranchNumberAt n` at `ofSlice u` is the germ
property `geometricBranchEq n` at `u`. -/
theorem hasGeometricBranchNumberAt_slice {S : Scheme.{u}} (n : ℕ) (U : Over S)
    (u : U.left) :
    hasGeometricBranchNumberAt n (GroupoidsOver.slice U) (Points.ofSlice u) ↔
      GermProperty.geometricBranchEq n U.left u :=
  sorry

/-- On `F.toGroupoids`, `hasGeometricBranchNumberAt n` at `ofAlgebraicSpace x` is
the étale-local germ property `geometricBranchEq n` of `F` at `x`. -/
theorem hasGeometricBranchNumberAt_toGroupoids {S : Scheme.{u}} (n : ℕ)
    (F : AlgebraicSpace S) (x : AlgebraicSpace.Points F) :
    hasGeometricBranchNumberAt n F.toGroupoids (Points.ofAlgebraicSpace x) ↔
      AlgebraicSpace.hasEtaleLocalAt (GermProperty.geometricBranchEq n)
        (GermProperty.IsSmoothLocal.isEtaleLocal
          (GermProperty.geometricBranchEq_isSmoothLocal n)) F x :=
  sorry

/-- The number of geometric branches of an algebraic stack `X` at a point `x`,
as the unique `n : ℕ` such that `hasGeometricBranchNumberAt n X x`, or else
`⊤`. -/
noncomputable def geometricBranchNumberAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' (setOf (fun n : ℕ => hasGeometricBranchNumberAt n X x)))

/-- The geometric branch number at `x` is a finite `n` if and only if some
smooth scheme chart through `x` has stalkwise geometric branch number `n` at
the source point. -/
theorem geometricBranchNumberAt_eq_nat_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} {n : ℕ} :
    geometricBranchNumberAt X x = n ↔ hasGeometricBranchNumberAt n X x :=
  sorry

/-- The geometric branch number at `x` is infinite if and only if
`hasGeometricBranchNumberAt n X x` fails for every `n`. -/
theorem geometricBranchNumberAt_eq_top_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    geometricBranchNumberAt X x = ⊤ ↔
      ∀ n : ℕ, ¬ hasGeometricBranchNumberAt n X x :=
  sorry

/-- The geometric branch number is the infimum of the finite geometric branch
numbers witnessed by smooth scheme charts through the point. -/
theorem geometricBranchNumberAt_def {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) :
    geometricBranchNumberAt X x =
      sInf ((fun n : ℕ => (n : ℕ∞)) '' (setOf (fun n : ℕ => hasGeometricBranchNumberAt n X x))) :=
  sorry

/-- On a scheme slice, the stack-theoretic geometric branch number recovers the
scheme-theoretic geometric branch number of any strict henselization of the
stalk. -/
theorem geometricBranchNumberAt_slice {S : Scheme.{u}} (U : Over S) (u : U.left)
    (Ash : Type u) [CommRing Ash] [Algebra (U.left.presheaf.stalk u) Ash]
    [IsStrictHenselizationOf (U.left.presheaf.stalk u) Ash] :
    geometricBranchNumberAt (GroupoidsOver.slice U) (Points.ofSlice u) =
      U.left.geometricBranchNumberAt u Ash :=
  sorry

/-- On `F.toGroupoids`, the stack-theoretic geometric branch number at the image
of a geometric point recovers the algebraic-space geometric branch number. -/
theorem geometricBranchNumberAt_toGroupoids {S : Scheme.{u}}
    (F : AlgebraicSpace S) (xbar : AlgebraicSpace.GeometricPoint F) :
    geometricBranchNumberAt F.toGroupoids
        (Points.ofAlgebraicSpace xbar.image) =
      F.geometricBranchNumberAt xbar :=
  sorry


end AlgebraicGeometry.AlgebraicStack
