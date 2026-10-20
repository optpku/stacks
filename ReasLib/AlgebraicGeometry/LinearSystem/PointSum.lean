/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.LinearSystem.VanishingLocus
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.FieldPoint
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Coincidence
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.PointSum
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheaf.Inclusion
public import ReasLib.AlgebraicGeometry.Scheme.Module.NegTwist
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Linear-system incidence with point-sum divisors

The universal point-sum divisor and the tautological zero scheme determine a
canonical incidence ideal on projective space times a cartesian power of a curve.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SchemeOverField
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LinearSystem

variable {k : Type u} [Field k]

/-- The morphism from `ℙ^n ×_k X^(r+1)` to `ℙ^n ×_k X^r` retaining the projective
coordinate and forgetting the zeroth curve coordinate. -/
noncomputable def pointSumProjection (X : SchemeOverField k) (n r : ℕ) :
    product (tensorPower X (r + 1)) n ⟶ product (tensorPower X r) n :=
  pullback.lift (fst (tensorPower X (r + 1)) n)
    (snd (tensorPower X (r + 1)) n ≫
      (CartesianMonoidalCategory.snd X (tensorPower X r)).left) (by
        exact pullback.condition.trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun f ↦ snd (tensorPower X (r + 1)) n ≫ f)
              (Over.w (CartesianMonoidalCategory.snd X (tensorPower X r))))).symm)

/-- The morphism from `ℙ^n ×_k X^(r+1)` to `ℙ^n ×_k X` retaining the projective
coordinate and the zeroth curve coordinate. -/
noncomputable def pointSumEvaluation (X : SchemeOverField k) (n r : ℕ) :
    product (tensorPower X (r + 1)) n ⟶ product X n :=
  pullback.lift (fst (tensorPower X (r + 1)) n)
    (snd (tensorPower X (r + 1)) n ≫ (coord X (r + 1) 0).left) (by
      rw [Category.assoc, Over.w]
      exact pullback.condition)

/-- The incidence ideal for containment of the universal point-sum divisor in the
zero scheme of the tautological linear combination of sections. -/
noncomputable def pointSumVanishingIdeal
    (X : SchemeOverField k) (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L) (r : ℕ) :
    (product (tensorPower X r) n).IdealSheafData :=
  let D1 := (coincidenceDivisor X r).comap (snd (tensorPower X (r + 1)) n)
  let D2 := (vanishingIdeal X L n s).comap (pointSumEvaluation X n r)
  D1.inclusionIdeal D2 (pointSumProjection X n r)

/-- The incidence ideal is the least base ideal whose pullback makes the universal
point-sum divisor lie in the tautological zero scheme. -/
theorem pointSumVanishingIdeal_le_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Projective X.hom] [Smooth X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L)
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ J : (product (tensorPower X r) n).IdealSheafData,
      pointSumVanishingIdeal X L n s r ≤ J ↔
        (vanishingIdeal X L n s).comap (pointSumEvaluation X n r) ≤
          (coincidenceDivisor X r).comap (snd (tensorPower X (r + 1)) n) ⊔
            J.comap (pointSumProjection X n r) :=
  sorry

/-- A closed point of the canonical incidence subscheme represents a linear
combination vanishing scheme-theoretically on the corresponding point-sum divisor,
with repeated coordinates contributing their full multiplicities. -/
theorem mem_pointSumVanishingIdeal_support_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Projective X.hom] [Smooth X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L)
    (r : ℕ) (hr : 1 ≤ r) :
      ∀ {v : Fin (n + 1) → k} (hv : v ≠ 0)
        {x : Fin r → X.left} (hx : ∀ i, x i ∈ closedPoints X.left)
        {z : product (tensorPower X r) n}
        (hz : z ∈ closedPoints (product (tensorPower X r) n)),
        fst (tensorPower X r) n z =
            ProjectiveSpace.homOf (RingHom.id k) hv (IsLocalRing.closedPoint k) →
          (∀ i, (coord X r i).left.base (snd (tensorPower X r) n z) = x i) →
            (z ∈ (pointSumVanishingIdeal X L n s r).support ↔
              Scheme.Modules.vanishesOnDivisor
                (linearCombination X L n s v) (Curve.pointSumDivisor X x hx)) :=
  sorry

/-- On a smooth projective curve over an algebraically closed field, any family of
sections of an invertible module determines a closed subscheme of `ℙ^n ×_k X^r`
whose closed points parametrize linear combinations vanishing on the point-sum
divisor, for every positive `r`. -/
theorem exists_vanishingOnPointSumLocus
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Projective X.hom] [Smooth X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (n : ℕ) (s : Fin (n + 1) → SchemeOverField.globalSectionsMod X L)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ Z : (product (tensorPower X r) n).IdealSheafData,
      ∀ {v : Fin (n + 1) → k} (hv : v ≠ 0)
        {x : Fin r → X.left} (hx : ∀ i, x i ∈ closedPoints X.left)
        {z : product (tensorPower X r) n}
        (hz : z ∈ closedPoints (product (tensorPower X r) n)),
        fst (tensorPower X r) n z =
            ProjectiveSpace.homOf (RingHom.id k) hv (IsLocalRing.closedPoint k) →
          (∀ i, (coord X r i).left.base (snd (tensorPower X r) n z) = x i) →
            (z ∈ Z.support ↔
              Scheme.Modules.vanishesOnDivisor
                (linearCombination X L n s v) (Curve.pointSumDivisor X x hx)) := by
  exact ⟨pointSumVanishingIdeal X L n s r,
    mem_pointSumVanishingIdeal_support_iff X L n s r hr⟩

end AlgebraicGeometry.LinearSystem
