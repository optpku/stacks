/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.AffineSpace.AdditiveGroup
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import stacks_project.Chap62.Lemma_62_4_1_Specialization
public import stacks_project.Chap62.Lemma_62_7_3_Equidimensional
public import stacks_project.Chap62.Lemma_62_7_3_Operations
public import stacks_project.Chap62.Remark_62_5_6_Support

/-!
# The affine line over the affine plane, with a fibrewise 0-cycle family

This file records the geometry of `X = 𝔸¹_S` over `S = 𝔸²_k` and the concrete
fibrewise 0-cycle family used as a counterexample to equidimensionality of
relative 0-cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open CyclesOnFibers
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineLineOverPlane

/-- The affine plane `S = 𝔸(2; Spec k)`, the Stacks `Spec(k[x, y])` base. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 2); Spec (.of k))

/-- The affine line `X = 𝔸(1; S)` over the affine plane, the Stacks
`Spec(k[x, y, t])` total space. -/
abbrev total (k : Type u) [Field k] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 1); base k)

/-- The structure morphism `X ⟶ S`. -/
abbrev hom (k : Type u) [Field k] : total k ⟶ base k :=
  total k ↘ base k

/-- The affine plane over a field is locally Noetherian. -/
instance instIsLocallyNoetherianBase (k : Type u) [Field k] :
    IsLocallyNoetherian (base k) :=
  sorry

/-- The origin `(0, 0)` of the affine plane, as the image of the closed point of
`Spec k` under the zero section. -/
def origin (k : Type u) [Field k] : base k :=
  (AffineSpace.zeroLeft (ULift.{u} (Fin 2)) (Spec (.of k)) :
      Spec (.of k) ⟶ base k)
    (IsLocalRing.closedPoint k)

/-- The standard `x`-coordinate on the affine plane. -/
def coordX (k : Type u) [Field k] : Γ(base k, ⊤) :=
  AffineSpace.coord (Spec (.of k)) (ULift.up (0 : Fin 2))

/-- The standard `y`-coordinate on the affine plane. -/
def coordY (k : Type u) [Field k] : Γ(base k, ⊤) :=
  AffineSpace.coord (Spec (.of k)) (ULift.up (1 : Fin 2))

/-- The image `a ∈ κ(s)` of the coordinate `x`. -/
def evalX (k : Type u) [Field k] (s : base k) : (base k).residueField s :=
  (base k).Γevaluation s (coordX k)

/-- The image `b ∈ κ(s)` of the coordinate `y`. -/
def evalY (k : Type u) [Field k] (s : base k) : (base k).residueField s :=
  (base k).Γevaluation s (coordY k)

/-- The affine-plane comparison with `Spec(k[x, y])`. -/
def baseSpecIso (k : Type u) [Field k] :
    base k ≅ Spec (.of (MvPolynomial (ULift.{u} (Fin 2)) k)) :=
  AffineSpace.SpecIso _ (.of k)

/-- The total-space comparison with the polynomial ring in one variable over
the global sections of the affine plane. -/
def totalSpecIso (k : Type u) [Field k] :
    total k ≅ Spec (.of (MvPolynomial (ULift.{u} (Fin 1)) Γ(base k, ⊤))) :=
  AffineSpace.isoOfIsAffine _ (base k)

/-- The scheme-theoretic fibre `X_s` is canonically the affine line over
`Spec κ(s)`. -/
def fiberIso (k : Type u) [Field k] (s : base k) :
    𝔸(ULift.{u} (Fin 1); Spec ((base k).residueField s)) ≅ (hom k).fiber s :=
  (AffineSpace.isPullback_map ((base k).fromSpecResidueField s)).isoPullback

/-- The comparison isomorphism identifies the affine line over `κ(s)` with the
scheme-theoretic fibre of `X ⟶ S`. -/
theorem fiberIso_spec (k : Type u) [Field k] (s : base k) :
    (fiberIso k s).hom ≫ (hom k).fiberι s =
      AffineSpace.map (ULift.{u} (Fin 1)) ((base k).fromSpecResidueField s) :=
  sorry

/-- The comparison isomorphism is a morphism over `Spec κ(s)`. -/
theorem fiberIso_hom_over (k : Type u) [Field k] (s : base k) :
    (fiberIso k s).hom ≫ (hom k).fiberToSpecResidueField s =
      𝔸(ULift.{u} (Fin 1); Spec ((base k).residueField s)) ↘
        Spec ((base k).residueField s) :=
  sorry

/-- The `κ`-rational point of the affine line with the given coordinate. -/
def affineLinePoint (K : Type u) [Field K] (c : K) :
    𝔸(ULift.{u} (Fin 1); Spec (.of K)) :=
  (AffineSpace.homOfVector (𝟙 (Spec (.of K))) fun _ ↦
      (Scheme.ΓSpecIso (.of K)).inv c)
    (IsLocalRing.closedPoint K)

/-- The `κ(s)`-rational point of the fibre with coordinate `t = a / b`. -/
def pointP (k : Type u) [Field k] (s : base k) (h : evalY k s ≠ 0) :
    (hom k).fiber s :=
  (fiberIso k s).hom
    (affineLinePoint _ (evalX k s * (Units.mk0 (evalY k s) h).val⁻¹))

/-- The `κ(s)`-rational point of the fibre with coordinate
`t = (a + b²) / b`. -/
def pointQ (k : Type u) [Field k] (s : base k) (h : evalY k s ≠ 0) :
    (hom k).fiber s :=
  (fiberIso k s).hom
    (affineLinePoint _
      ((evalX k s + evalY k s ^ 2) * (Units.mk0 (evalY k s) h).val⁻¹))

/-- The origin of the affine plane evaluates the `x`-coordinate to `0`. -/
theorem evalX_origin (k : Type u) [Field k] : evalX k (origin k) = 0 := sorry

/-- The origin of the affine plane evaluates the `y`-coordinate to `0`. -/
theorem evalY_origin (k : Type u) [Field k] : evalY k (origin k) = 0 := sorry

/-- The point `p` is 0-dimensional on the scheme-theoretic fibre. -/
theorem pointP_fiberCycleDimension (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) :
    (hom k).fiberCycleDimension s (pointP k s h) = 0 :=
  sorry

/-- The point `q` is 0-dimensional on the scheme-theoretic fibre. -/
theorem pointQ_fiberCycleDimension (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) :
    (hom k).fiberCycleDimension s (pointQ k s h) = 0 :=
  sorry

/-- The family `α` of 0-cycles on fibres of `X / S`, with `α_s = 0` if `b = 0`
and `α_s = [p] - [q]` otherwise. -/
def family (k : Type u) [Field k] : CyclesOnFibers (hom k) (0 : ℕ) :=
  fun s ↦
    @dite _ (evalY k s = 0) (Classical.propDecidable _)
      (fun _ ↦ 0)
      (fun h ↦
        CycleGroup.point ((hom k).fiberCycleDimension s) 0 (pointP k s h)
            (pointP_fiberCycleDimension k s h) -
          CycleGroup.point ((hom k).fiberCycleDimension s) 0 (pointQ k s h)
            (pointQ_fiberCycleDimension k s h))

/-- Evaluating the family recovers the piecewise formula `0` or `[p] - [q]`. -/
theorem family_apply (k : Type u) [Field k] (s : base k) :
    family k s =
      @dite _ (evalY k s = 0) (Classical.propDecidable _)
        (fun _ ↦ 0)
        (fun h ↦
          CycleGroup.point ((hom k).fiberCycleDimension s) 0 (pointP k s h)
              (pointP_fiberCycleDimension k s h) -
            CycleGroup.point ((hom k).fiberCycleDimension s) 0 (pointQ k s h)
              (pointQ_fiberCycleDimension k s h)) :=
  sorry

/-- The family vanishes on a fibre if and only if the image of `y` is zero. -/
theorem family_eq_zero_iff (k : Type u) [Field k] (s : base k) :
    family k s = 0 ↔ evalY k s = 0 :=
  sorry

/-- Off the locus `b = 0`, the coefficient of `p` is `1`. -/
theorem family_coeff_pointP (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) :
    CyclesOnFibers.toAlgebraicCycle (family k) s (pointP k s h) = 1 :=
  sorry

/-- Off the locus `b = 0`, the coefficient of `q` is `-1`. -/
theorem family_coeff_pointQ (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) :
    CyclesOnFibers.toAlgebraicCycle (family k) s (pointQ k s h) = -1 :=
  sorry

/-- Off the locus `b = 0`, every point other than `p` and `q` has coefficient
`0`. -/
theorem family_coeff_eq_zero_of_ne (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) {x : (hom k).fiber s}
    (hxP : x ≠ pointP k s h) (hxQ : x ≠ pointQ k s h) :
    CyclesOnFibers.toAlgebraicCycle (family k) s x = 0 :=
  sorry

end AlgebraicGeometry.AffineLineOverPlane
