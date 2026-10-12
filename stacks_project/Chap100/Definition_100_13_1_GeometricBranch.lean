/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import stacks_project.Chap66.Definition_66_23_4_GeometricBranch
public import stacks_project.Chap66.Remark_66_7_6_LocalRing
public import stacks_project.Chap100.Definition_100_7_5_SmoothLocal

/-!
# Geometric branch numbers of algebraic stacks at a point

The number of geometric branches of an algebraic stack at a point is the unique
`n : ℕ` such that the smooth-local germ property `P_n` holds in the sense of
Lemma 100.7.4, or else `⊤`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A local ring has geometric branch number `n` if some strict henselization
has exactly `n` minimal primes. -/
def hasGeometricBranchNumber (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∃ (Ash : Type u) (_ : CommRing Ash) (_ : Algebra R Ash)
    (_ : IsStrictHenselizationOf R Ash), geometricBranchNumber R Ash = n

/-- `hasGeometricBranchNumber n R` is the existence of a strict henselization of
`R` with geometric branch number `n`. -/
theorem hasGeometricBranchNumber_def (n : ℕ) (R : Type u) [CommRing R]
    [IsLocalRing R] :
    hasGeometricBranchNumber n R ↔
      ∃ (Ash : Type u) (_ : CommRing Ash) (_ : Algebra R Ash)
        (_ : IsStrictHenselizationOf R Ash), geometricBranchNumber R Ash = n :=
  sorry

namespace hasGeometricBranchNumber

/-- A strict henselization of `R` with geometric branch number `n` witnesses
`hasGeometricBranchNumber n R`. -/
theorem of {n : ℕ} {R : Type u} [CommRing R] [IsLocalRing R] (Ash : Type u)
    [CommRing Ash] [Algebra R Ash] [IsStrictHenselizationOf R Ash]
    (h : geometricBranchNumber R Ash = n) : hasGeometricBranchNumber n R :=
  sorry

/-- A local ring with geometric branch number `n` admits a strict henselization
with that geometric branch number. -/
theorem spec {n : ℕ} {R : Type u} [CommRing R] [IsLocalRing R]
    (h : hasGeometricBranchNumber n R) :
    ∃ (Ash : Type u) (_ : CommRing Ash) (_ : Algebra R Ash)
      (_ : IsStrictHenselizationOf R Ash), geometricBranchNumber R Ash = n :=
  sorry

/-- At most one natural number is the geometric branch number of a local ring. -/
theorem unique {R : Type u} [CommRing R] [IsLocalRing R] {n m : ℕ}
    (hn : hasGeometricBranchNumber n R) (hm : hasGeometricBranchNumber m R) :
    n = m :=
  sorry

end hasGeometricBranchNumber

/-- The geometric branch number of a local ring is independent of the chosen
strict henselization: it equals `n` for some strict henselization if and only
if it equals `n` for every strict henselization. -/
theorem hasGeometricBranchNumber_iff (n : ℕ) (R : Type u) [CommRing R]
    [IsLocalRing R] :
    hasGeometricBranchNumber n R ↔
      ∀ (Ash : Type u) [CommRing Ash] [Algebra R Ash]
        [IsStrictHenselizationOf R Ash], geometricBranchNumber R Ash = n :=
  sorry

namespace GermProperty

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

end GermProperty

namespace AlgebraicStack

/-- An algebraic stack `X` has geometric branch number `n` at `x` when the
equivalent conditions of Lemma 100.7.4 hold for `GermProperty.geometricBranchEq n`. -/
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

/-- The finite geometric branch number extracted from a witness of
`hasGeometricBranchNumberAt`. -/
noncomputable def geometricBranchNumberAtNat {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X}
    (h : ∃ n : ℕ, hasGeometricBranchNumberAt n X x) : ℕ :=
  Classical.choose h

/-- The extracted finite value satisfies `hasGeometricBranchNumberAt`. -/
theorem geometricBranchNumberAtNat_spec {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X}
    (h : ∃ n : ℕ, hasGeometricBranchNumberAt n X x) :
    hasGeometricBranchNumberAt (geometricBranchNumberAtNat h) X x :=
  sorry

/-- The number of geometric branches of an algebraic stack `X` at a point `x`,
as the unique `n : ℕ` such that `hasGeometricBranchNumberAt n X x`, or else
`⊤`. -/
noncomputable def geometricBranchNumberAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : ℕ∞ :=
  @dite ℕ∞ (∃ n : ℕ, hasGeometricBranchNumberAt n X x) (Classical.dec _)
    (fun h ↦ geometricBranchNumberAtNat h) (fun _ ↦ ⊤)

/-- The geometric branch number at `x` is a finite `n` if and only if the
equivalent conditions of Lemma 100.7.4 hold for `geometricBranchEq n`. -/
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

/-- Unfolding of `geometricBranchNumberAt` as the unique finite value of
`hasGeometricBranchNumberAt`, or else `⊤`. -/
theorem geometricBranchNumberAt_def {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) :
    geometricBranchNumberAt X x =
      @dite ℕ∞ (∃ n : ℕ, hasGeometricBranchNumberAt n X x) (Classical.dec _)
        (fun h ↦ geometricBranchNumberAtNat h) (fun _ ↦ ⊤) :=
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

end AlgebraicStack

end AlgebraicGeometry
