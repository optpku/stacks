/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap111.Exercise_111_39_1_FieldPoint
public import stacks_project.Chap111.Exercise_111_46_1_VanishingLocus
public import stacks_project.Chap111.Exercise_111_46_2_Coincidence
public import stacks_project.Chap111.Exercise_111_46_4_NegTwist
public import stacks_project.Chap111.Exercise_111_46_4_PointSum

/-!
# Closed points of the linear-system incidence locus on `ℙ^n × X^r`

The closed-point characterisation of the incidence subscheme of a linear
system against the point-sum divisor on `ℙ^n ×_k X^r`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LinearSystem

/-- Exercise 111.46.4: let `k` be an algebraically closed field, let `X` be a
smooth projective curve over `k`, let `L` be an invertible `𝒪_X`-module, and let
`s 0, …, s n` be global sections of `L`. For `r ≥ 1` there is a natural closed
subscheme `Z ⊂ ℙ^n ×_k X^r` whose closed points `((v 0 : … : v n), x 1, …, x r)`
are exactly those for which the section `v 0 • s 0 + ⋯ + v n • s n` vanishes on
the divisor `D = x 1 + ⋯ + x r`, i.e. lies in `L(-D)`. -/
@[stacks 0EGC]
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
                (linearCombination X L n s v) (Curve.pointSumDivisor X x hx)) :=
  sorry

end AlgebraicGeometry.LinearSystem
