/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.ENat.Lattice
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty.GeometricBranch
public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricBranch
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricBranch.Characterization
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
  Iff.rfl

namespace hasGeometricBranchNumberAt

/-- A smooth morphism from a scheme through `x` on which the source has
geometric branch number `n` witnesses `hasGeometricBranchNumberAt n X x`. -/
theorem of {S : Scheme.{u}} {n : ℕ} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} {U : Over S} (p : GroupoidsOver.slice U ⟶ X) (u : U.left)
    [Groupoids.Hom.Smooth p] (hx : Points.mapSlice p u = x)
    (hPu : GermProperty.geometricBranchEq n U.left u) :
    hasGeometricBranchNumberAt n X x :=
  existsSmoothAt.of p u hx hPu

/-- An algebraic stack satisfying `hasGeometricBranchNumberAt n X x` admits a
smooth scheme chart through `x` on which the source has geometric branch number
`n`. -/
theorem spec {S : Scheme.{u}} {n : ℕ} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : hasGeometricBranchNumberAt n X x) :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
      Groupoids.Hom.Smooth p ∧ Points.mapSlice p u = x ∧
        GermProperty.geometricBranchEq n U.left u :=
  h

/-- At most one natural number is the geometric branch number of `X` at `x`. -/
theorem unique {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} {n m : ℕ} (hn : hasGeometricBranchNumberAt n X x)
    (hm : hasGeometricBranchNumberAt m X x) : n = m := by
  obtain ⟨U, p, u, hp, hx, hu⟩ := hn.spec
  have hm' : GermProperty.geometricBranchEq m U.left u :=
    ((forallSmoothAt_iff_existsSmoothAt (GermProperty.geometricBranchEq m)
      (GermProperty.geometricBranchEq_isSmoothLocal m) X x).mpr hm) U p u hp hx
  exact _root_.hasGeometricBranchNumber.unique hu hm'

end hasGeometricBranchNumberAt

/-- `hasGeometricBranchNumberAt n X x` if and only if every smooth scheme chart
through `x` has geometric branch number `n` at the source point. -/
theorem hasGeometricBranchNumberAt_iff_forallSmoothAt {S : Scheme.{u}} (n : ℕ)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    hasGeometricBranchNumberAt n X x ↔
      forallSmoothAt (GermProperty.geometricBranchEq n) X x :=
  (forallSmoothAt_iff_existsSmoothAt (GermProperty.geometricBranchEq n)
    (GermProperty.geometricBranchEq_isSmoothLocal n) X x).symm

/-- `hasGeometricBranchNumberAt n X x` if and only if some smooth scheme chart
through `x` has geometric branch number `n` at the source point. -/
theorem hasGeometricBranchNumberAt_iff_existsSmoothAt {S : Scheme.{u}} (n : ℕ)
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    hasGeometricBranchNumberAt n X x ↔
      existsSmoothAt (GermProperty.geometricBranchEq n) X x :=
  Iff.rfl

/-- `hasGeometricBranchNumberAt n X x` if and only if some smooth algebraic-space
chart through `x` has geometric branch number `n` at the source point. -/
theorem hasGeometricBranchNumberAt_iff_existsSmoothSpaceAt {S : Scheme.{u}}
    (n : ℕ) (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    hasGeometricBranchNumberAt n X x ↔
      existsSmoothSpaceAt (GermProperty.geometricBranchEq n) X x :=
  existsSmoothAt_iff_existsSmoothSpaceAt (GermProperty.geometricBranchEq n)
    (GermProperty.geometricBranchEq_isSmoothLocal n) X x

/-- On a scheme slice, `hasGeometricBranchNumberAt n` at `ofSlice u` is the germ
property `geometricBranchEq n` at `u`. -/
theorem hasGeometricBranchNumberAt_slice {S : Scheme.{u}} (n : ℕ) (U : Over S)
    (u : U.left) :
    hasGeometricBranchNumberAt n (GroupoidsOver.slice U) (Points.ofSlice u) ↔
      GermProperty.geometricBranchEq n U.left u :=
  existsSmoothAt_slice (GermProperty.geometricBranchEq n)
    (GermProperty.geometricBranchEq_isSmoothLocal n) U u

/-- On `F.toGroupoids`, `hasGeometricBranchNumberAt n` at `ofAlgebraicSpace x` is
the étale-local germ property `geometricBranchEq n` of `F` at `x`. -/
theorem hasGeometricBranchNumberAt_toGroupoids {S : Scheme.{u}} (n : ℕ)
    (F : AlgebraicSpace S) (x : AlgebraicSpace.Points F) :
    hasGeometricBranchNumberAt n F.toGroupoids (Points.ofAlgebraicSpace x) ↔
      AlgebraicSpace.hasEtaleLocalAt (GermProperty.geometricBranchEq n)
        (GermProperty.IsSmoothLocal.isEtaleLocal
          (GermProperty.geometricBranchEq_isSmoothLocal n)) F x :=
  existsSmoothAt_toGroupoids (GermProperty.geometricBranchEq n)
    (GermProperty.geometricBranchEq_isSmoothLocal n) F x

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
    geometricBranchNumberAt X x = n ↔ hasGeometricBranchNumberAt n X x := by
  constructor
  · show geometricBranchNumberAt X x = n → hasGeometricBranchNumberAt n X x
    intro h
    have hs : ((fun m : ℕ => (m : ℕ∞)) ''
        {m | hasGeometricBranchNumberAt m X x}).Nonempty := by
      by_contra hempty
      have htop : geometricBranchNumberAt X x = ⊤ := by
        simp [geometricBranchNumberAt, Set.not_nonempty_iff_eq_empty.mp hempty]
      exact ENat.coe_ne_top n (h.symm.trans htop)
    obtain ⟨m, hm, he⟩ := csInf_mem hs
    have hmn : m = n := ENat.coe_inj.mp (he.trans h)
    exact hmn ▸ hm
  · show hasGeometricBranchNumberAt n X x → geometricBranchNumberAt X x = n
    intro hn
    apply le_antisymm
    · change geometricBranchNumberAt X x ≤ (n : ℕ∞)
      exact sInf_le ⟨n, hn, rfl⟩
    · change (n : ℕ∞) ≤ geometricBranchNumberAt X x
      refine le_sInf ?_
      rintro _ ⟨m, hm, rfl⟩
      exact (congrArg (fun k : ℕ => (k : ℕ∞))
        (hasGeometricBranchNumberAt.unique hn hm)).le

/-- The geometric branch number at `x` is infinite if and only if
`hasGeometricBranchNumberAt n X x` fails for every `n`. -/
theorem geometricBranchNumberAt_eq_top_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    geometricBranchNumberAt X x = ⊤ ↔
      ∀ n : ℕ, ¬ hasGeometricBranchNumberAt n X x := by
  constructor
  · show geometricBranchNumberAt X x = ⊤ →
      ∀ n : ℕ, ¬ hasGeometricBranchNumberAt n X x
    intro h n hn
    have hle : geometricBranchNumberAt X x ≤ (n : ℕ∞) :=
      sInf_le ⟨n, hn, rfl⟩
    rw [h] at hle
    exact ENat.coe_ne_top n (top_le_iff.mp hle)
  · show (∀ n : ℕ, ¬ hasGeometricBranchNumberAt n X x) →
      geometricBranchNumberAt X x = ⊤
    intro h
    have hempty : (fun n : ℕ => (n : ℕ∞)) ''
        {n | hasGeometricBranchNumberAt n X x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨n, hn, rfl⟩
      exact h n hn
    simp [geometricBranchNumberAt, hempty]

/-- The geometric branch number is the infimum of the finite geometric branch
numbers witnessed by smooth scheme charts through the point. -/
theorem geometricBranchNumberAt_def {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) :
    geometricBranchNumberAt X x =
      sInf ((fun n : ℕ => (n : ℕ∞)) '' (setOf (fun n : ℕ => hasGeometricBranchNumberAt n X x))) :=
  rfl

/-- On a scheme slice, the stack-theoretic geometric branch number recovers the
scheme-theoretic geometric branch number of any strict henselization of the
stalk. -/
theorem geometricBranchNumberAt_slice {S : Scheme.{u}} (U : Over S) (u : U.left)
    (Ash : Type u) [CommRing Ash] [Algebra (U.left.presheaf.stalk u) Ash]
    [IsStrictHenselizationOf (U.left.presheaf.stalk u) Ash] :
    geometricBranchNumberAt (GroupoidsOver.slice U) (Points.ofSlice u) =
      U.left.geometricBranchNumberAt u Ash := by
  cases h : U.left.geometricBranchNumberAt u Ash with
  | top =>
    show geometricBranchNumberAt (GroupoidsOver.slice U) (Points.ofSlice u) = ⊤
    apply geometricBranchNumberAt_eq_top_iff.mpr
    intro n hn
    have hu : _root_.hasGeometricBranchNumber n (U.left.presheaf.stalk u) :=
      (hasGeometricBranchNumberAt_slice n U u).mp hn
    have he : geometricBranchNumber (U.left.presheaf.stalk u) Ash = n :=
      (hasGeometricBranchNumber_iff n (U.left.presheaf.stalk u)).mp hu Ash
    exact ENat.coe_ne_top n (h.symm.trans he).symm
  | coe n =>
    show geometricBranchNumberAt (GroupoidsOver.slice U) (Points.ofSlice u) = n
    apply geometricBranchNumberAt_eq_nat_iff.mpr
    apply (hasGeometricBranchNumberAt_slice n U u).mpr
    exact ⟨Ash, inferInstance, inferInstance, inferInstance, h⟩

/-- On `F.toGroupoids`, the stack-theoretic geometric branch number at the image
of a geometric point recovers the algebraic-space geometric branch number. -/
theorem geometricBranchNumberAt_toGroupoids {S : Scheme.{u}}
    (F : AlgebraicSpace S) (xbar : AlgebraicSpace.GeometricPoint F) :
    geometricBranchNumberAt F.toGroupoids
        (Points.ofAlgebraicSpace xbar.image) =
      F.geometricBranchNumberAt xbar := by
  have hetale (U : Over S) (a : AlgebraicSpace.ofOver U ⟶ F) :
      AlgebraicSpace.Etale a ↔
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a := by
    constructor
    · show AlgebraicSpace.Etale a →
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a
      intro ha
      have hid : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
          (𝟙 (yoneda.obj U)) := by
        change (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale)
          (Over.forget S)).presheaf (𝟙 (yoneda.obj U))
        exact MorphismProperty.id_mem _ _
      simpa only [AlgebraicSpace.ofOver, AlgebraicSpace.ofFunctor,
        AlgebraicSpace.functorOfPoints, Category.id_comp] using
        ha.of_etale (𝟙 (yoneda.obj U)) hid
    · show (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
        AlgebraicSpace.Etale a
      intro ha
      refine ⟨fun φ hφ => ?_⟩
      change (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale)
        (Over.forget S)).presheaf (φ ≫ a)
      exact MorphismProperty.comp_mem _ φ a hφ ha
  have hfinite (n : ℕ) (hn : 0 < n) :
      geometricBranchNumberAt F.toGroupoids (Points.ofAlgebraicSpace xbar.image) = n ↔
        F.geometricBranchNumber xbar.image = n := by
    rw [geometricBranchNumberAt_eq_nat_iff,
      hasGeometricBranchNumberAt_toGroupoids,
      AlgebraicSpace.geometricBranchNumber_eq_nat_iff_geometricBranchNumber _ n hn]
    constructor
    · show AlgebraicSpace.hasEtaleLocalAt (GermProperty.geometricBranchEq n) _ F
          xbar.image → AlgebraicSpace.geometricBranchNumberEq xbar.image n
      intro h U a u ha hx
      have hu := (AlgebraicSpace.forallEtaleAt_iff_existsEtaleAt
        (GermProperty.geometricBranchEq n)
        (GermProperty.IsSmoothLocal.isEtaleLocal
          (GermProperty.geometricBranchEq_isSmoothLocal n)) F xbar.image).mpr h
      exact (hasGeometricBranchNumber_iff n (U.left.presheaf.stalk u)).mp
        (hu U a u ((hetale U a).mp ha) hx)
    · show AlgebraicSpace.geometricBranchNumberEq xbar.image n →
        AlgebraicSpace.hasEtaleLocalAt (GermProperty.geometricBranchEq n) _ F xbar.image
      intro h
      apply (AlgebraicSpace.forallEtaleAt_iff_existsEtaleAt
        (GermProperty.geometricBranchEq n)
        (GermProperty.IsSmoothLocal.isEtaleLocal
          (GermProperty.geometricBranchEq_isSmoothLocal n)) F xbar.image).mp
      intro U a u ha hx
      exact (hasGeometricBranchNumber_iff n (U.left.presheaf.stalk u)).mpr
        (h U a u ((hetale U a).mpr ha) hx)
  have hpos {n : ℕ}
      (h : hasGeometricBranchNumberAt n F.toGroupoids
        (Points.ofAlgebraicSpace xbar.image)) : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hn
    obtain ⟨U, p, u, _, _, Ash, hRing, hAlg, hStrict, hcount⟩ := h.spec
    letI := hRing
    letI := hAlg
    letI := hStrict
    obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes (bot_ne_top : (⊥ : Ideal Ash) ≠ ⊤)
    have hne : (minimalPrimes Ash).encard ≠ 0 :=
      Set.encard_ne_zero.mpr ⟨q, hq⟩
    exact hne (by simpa only [hn, Nat.cast_zero] using hcount)
  rw [← AlgebraicSpace.geometricBranchNumber_eq_geometricBranchNumberAt
    xbar.image xbar rfl]
  cases h : F.geometricBranchNumber xbar.image with
  | top =>
    change geometricBranchNumberAt F.toGroupoids (Points.ofAlgebraicSpace xbar.image) = ⊤
    apply geometricBranchNumberAt_eq_top_iff.mpr
    intro n hn
    have he := (hfinite n (hpos hn)).mp (geometricBranchNumberAt_eq_nat_iff.mpr hn)
    exact ENat.coe_ne_top n (h.symm.trans he).symm
  | coe n =>
    change geometricBranchNumberAt F.toGroupoids (Points.ofAlgebraicSpace xbar.image) = n
    have hn : 0 < n := Nat.pos_of_ne_zero fun hn =>
      AlgebraicSpace.geometricBranchNumber_ne_zero xbar.image
        (by simpa only [hn, Nat.cast_zero] using h)
    exact (hfinite n hn).mpr h


end AlgebraicGeometry.AlgebraicStack
