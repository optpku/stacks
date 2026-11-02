/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.AffineSpace.AdditiveGroup
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.RelativeCycle.Equidimensional
import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Section
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# A non-equidimensional relative cycle on the affine line over the affine plane

Over an arbitrary field, the difference of the rational-point cycles with coordinates
`a / b` and `(a + b²) / b`, extended by zero where `b = 0`, is a relative
zero-cycle whose support closure contains the entire fibre over the origin.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Hom
open CyclesOnFibers
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineLineOverPlane

/-- The affine plane over a field, with coordinates `x` and `y`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 2); Spec (.of k))

/-- The affine line over the affine plane, with fibre coordinate `t`. -/
abbrev total (k : Type u) [Field k] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 1); base k)

/-- The canonical projection from the affine line to the affine plane. -/
abbrev hom (k : Type u) [Field k] : total k ⟶ base k :=
  total k ↘ base k

/-- The affine plane over a field is locally Noetherian. -/
instance instIsLocallyNoetherianBase (k : Type u) [Field k] :
    IsLocallyNoetherian (base k) :=
  LocallyOfFiniteType.isLocallyNoetherian (base k ↘ Spec (.of k))

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

/-- The scheme-theoretic fibre is canonically the affine line over `Spec κ(s)`. -/
def fiberIso (k : Type u) [Field k] (s : base k) :
    𝔸(ULift.{u} (Fin 1); Spec ((base k).residueField s)) ≅ (hom k).fiber s :=
  (AffineSpace.isPullback_map ((base k).fromSpecResidueField s)).isoPullback

/-- The comparison isomorphism identifies the fibre inclusion with the
base-change map from the affine line over `κ(s)`. -/
theorem fiberIso_spec (k : Type u) [Field k] (s : base k) :
    (fiberIso k s).hom ≫ (hom k).fiberι s =
      AffineSpace.map (ULift.{u} (Fin 1)) ((base k).fromSpecResidueField s) :=
  (AffineSpace.isPullback_map ((base k).fromSpecResidueField s)).isoPullback_hom_fst

/-- The comparison isomorphism is a morphism over `Spec κ(s)`. -/
theorem fiberIso_hom_over (k : Type u) [Field k] (s : base k) :
    (fiberIso k s).hom ≫ (hom k).fiberToSpecResidueField s =
      𝔸(ULift.{u} (Fin 1); Spec ((base k).residueField s)) ↘
        Spec ((base k).residueField s) :=
  (AffineSpace.isPullback_map ((base k).fromSpecResidueField s)).isoPullback_hom_snd

/-- The rational point of the affine line with the given coordinate. -/
def affineLinePoint (K : Type u) [Field K] (c : K) :
    𝔸(ULift.{u} (Fin 1); Spec (.of K)) :=
  (AffineSpace.homOfVector (𝟙 (Spec (.of K))) fun _ ↦
      (Scheme.ΓSpecIso (.of K)).inv c)
    (IsLocalRing.closedPoint K)

private theorem affineLinePoint_injective (K : Type u) [Field K] :
    Function.Injective (affineLinePoint K) := by
  intro c d he
  let S := Spec (.of K)
  let A := 𝔸(ULift.{u} (Fin 1); S)
  let o : S := IsLocalRing.closedPoint K
  let p (z : K) : S ⟶ A :=
    AffineSpace.homOfVector (𝟙 S) fun _ ↦ (Scheme.ΓSpecIso (.of K)).inv z
  let t : Γ(A, ⊤) := AffineSpace.coord S (ULift.up (0 : Fin 1))
  let c₀ : Γ(A, ⊤) := (A ↘ S).appTop ((Scheme.ΓSpecIso (.of K)).inv c)
  have hp (z w : K) :
      (p z).appTop ((A ↘ S).appTop ((Scheme.ΓSpecIso (.of K)).inv w)) =
        (Scheme.ΓSpecIso (.of K)).inv w := by
    change ((A ↘ S).appTop ≫ (p z).appTop) _ = _
    rw [← Scheme.Hom.comp_appTop]
    change ((p z) ≫ (𝔸(ULift.{u} (Fin 1); S) ↘ S)).appTop _ = _
    rw [AffineSpace.homOfVector_over]
    rfl
  have ht (z : K) : (p z).appTop t = (Scheme.ΓSpecIso (.of K)).inv z :=
    AffineSpace.homOfVector_appTop_coord _ _ _
  have hc : A.Γevaluation (affineLinePoint K c) (t - c₀) = 0 := by
    change A.Γevaluation ((p c) o) (t - c₀) = 0
    apply ((p c).residueFieldMap o).hom.injective
    rw [map_zero, Scheme.Γevaluation_naturality_apply]
    simp only [map_sub, ht, c₀, hp, sub_self, map_zero]
  have hd : S.Γevaluation o ((p d).appTop (t - c₀)) = 0 := by
    rw [← Scheme.Γevaluation_naturality_apply (p d) o]
    have hc' : A.Γevaluation ((p d) o) (t - c₀) = 0 := by
      change A.Γevaluation (affineLinePoint K d) (t - c₀) = 0
      rw [← he]
      exact hc
    rw [hc', map_zero]
  have hz : d - c = 0 := by
    apply (((Scheme.ΓSpecIso (.of K)).inv ≫ S.Γevaluation o).hom.injective)
    change S.Γevaluation o ((Scheme.ΓSpecIso (.of K)).inv (d - c)) =
      S.Γevaluation o ((Scheme.ΓSpecIso (.of K)).inv 0)
    simp only [map_sub, map_zero]
    simpa only [map_sub, ht, c₀, hp] using hd
  exact (sub_eq_zero.mp hz).symm

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

private theorem pointP_ne_pointQ (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) : pointP k s h ≠ pointQ k s h := by
  intro he
  have hc := affineLinePoint_injective ((base k).residueField s)
    ((fiberIso k s).hom.homeomorph.injective he)
  change evalX k s * (evalY k s)⁻¹ =
    (evalX k s + evalY k s ^ 2) * (evalY k s)⁻¹ at hc
  have heq : evalX k s = evalX k s + evalY k s ^ 2 :=
    mul_right_cancel₀ (inv_ne_zero h) hc
  have hy2 : evalY k s ^ 2 = 0 :=
    add_left_cancel (heq.symm.trans (add_zero _).symm)
  exact (pow_ne_zero 2 h) hy2

/-- The origin of the affine plane evaluates the `x`-coordinate to `0`. -/
theorem evalX_origin (k : Type u) [Field k] : evalX k (origin k) = 0 := by
  let o : Spec (.of k) := IsLocalRing.closedPoint k
  let z : Spec (.of k) ⟶ base k := AffineSpace.homOfVector (𝟙 _) fun _ ↦ 0
  change (base k).Γevaluation (z o) (coordX k) = 0
  apply (z.residueFieldMap o).hom.injective
  rw [map_zero, Scheme.Γevaluation_naturality_apply]
  simp [z, coordX]

/-- The origin of the affine plane evaluates the `y`-coordinate to `0`. -/
theorem evalY_origin (k : Type u) [Field k] : evalY k (origin k) = 0 := by
  let o : Spec (.of k) := IsLocalRing.closedPoint k
  let z : Spec (.of k) ⟶ base k := AffineSpace.homOfVector (𝟙 _) fun _ ↦ 0
  change (base k).Γevaluation (z o) (coordY k) = 0
  apply (z.residueFieldMap o).hom.injective
  rw [map_zero, Scheme.Γevaluation_naturality_apply]
  simp [z, coordY]

private theorem section_dimension {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (e : Y ⟶ X) (he : e ≫ f = 𝟙 _) (y : Y) :
    f.relativeDimensionFunction (fun _ ↦ 0) (e y) = 0 := by
  have hsurj := (residueFieldMap_bijective_of_section e f he y).surjective
  haveI : Algebra.IsAlgebraic (Y.residueField (f (e y))) (X.residueField (e y)) := by
    constructor
    intro z
    obtain ⟨a, rfl⟩ := hsurj z
    exact isAlgebraic_algebraMap a
  simp [relativeDimensionFunction, residueFieldTranscendenceDegreeAt, trdeg_eq_zero]

private theorem fiberPoint_dimension (k : Type u) [Field k] (s : base k) (c : (base k).residueField s) :
    (hom k).fiberCycleDimension s ((fiberIso k s).hom (affineLinePoint _ c)) = 0 := by
  letI : LocallyOfFiniteType ((hom k).fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (hom k) ((base k).fromSpecResidueField s)))
  let e : Spec ((base k).residueField s) ⟶ (hom k).fiber s :=
    (AffineSpace.homOfVector (𝟙 _) fun _ ↦ (Scheme.ΓSpecIso ((base k).residueField s)).inv c) ≫
      (fiberIso k s).hom
  exact section_dimension ((hom k).fiberToSpecResidueField s) e
    (by
      dsimp only [e]
      rw [Category.assoc, fiberIso_hom_over, AffineSpace.homOfVector_over])
    (IsLocalRing.closedPoint ((base k).residueField s))

/-- The point `p` is zero-dimensional on the scheme-theoretic fibre. -/
theorem pointP_fiberCycleDimension (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) :
    (hom k).fiberCycleDimension s (pointP k s h) = 0 :=
  fiberPoint_dimension k s _

/-- The point `q` is zero-dimensional on the scheme-theoretic fibre. -/
theorem pointQ_fiberCycleDimension (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) :
    (hom k).fiberCycleDimension s (pointQ k s h) = 0 :=
  fiberPoint_dimension k s _

open scoped Classical in
/-- The family of zero-cycles on fibres with value zero if `b = 0` and
value `[p] - [q]` otherwise. -/
def family (k : Type u) [Field k] : CyclesOnFibers (hom k) (0 : ℕ) :=
  fun s ↦
    if h : evalY k s = 0 then 0
    else
      CycleGroup.point ((hom k).fiberCycleDimension s) 0 (pointP k s h)
          (pointP_fiberCycleDimension k s h) -
        CycleGroup.point ((hom k).fiberCycleDimension s) 0 (pointQ k s h)
          (pointQ_fiberCycleDimension k s h)

open scoped Classical in
/-- Evaluating the family recovers the piecewise formula `0` or `[p] - [q]`. -/
theorem family_apply (k : Type u) [Field k] (s : base k) :
    family k s =
      if h : evalY k s = 0 then 0
      else
        CycleGroup.point ((hom k).fiberCycleDimension s) 0 (pointP k s h)
            (pointP_fiberCycleDimension k s h) -
          CycleGroup.point ((hom k).fiberCycleDimension s) 0 (pointQ k s h)
            (pointQ_fiberCycleDimension k s h) :=
  rfl

/-- The family vanishes on a fibre if and only if the image of `y` is zero. -/
theorem family_eq_zero_iff (k : Type u) [Field k] (s : base k) :
    family k s = 0 ↔ evalY k s = 0 := by
  classical
  constructor
  · intro hzero
    by_contra h
    have hcoeff := congrArg
      (fun z : CycleGroup ((hom k).fiber s) ((hom k).fiberCycleDimension s) 0 ↦
        CycleGroup.toAlgebraicCycle _ _ z (pointP k s h)) hzero
    simpa [family, h, CycleGroup.toAlgebraicCycle, CycleGroup.point,
      pointP_ne_pointQ k s h] using hcoeff
  · intro h
    simp [family, h]

/-- Off the locus `b = 0`, the coefficient of `p` is `1`. -/
theorem family_coeff_pointP (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) :
    CyclesOnFibers.toAlgebraicCycle (family k) s (pointP k s h) = 1 := by
  classical
  simp [CyclesOnFibers.toAlgebraicCycle, family, h, CycleGroup.toAlgebraicCycle,
    CycleGroup.point, pointP_ne_pointQ k s h]

/-- Off the locus `b = 0`, the coefficient of `q` is `-1`. -/
theorem family_coeff_pointQ (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) :
    CyclesOnFibers.toAlgebraicCycle (family k) s (pointQ k s h) = -1 := by
  classical
  simp [CyclesOnFibers.toAlgebraicCycle, family, h, CycleGroup.toAlgebraicCycle,
    CycleGroup.point, (pointP_ne_pointQ k s h).symm]

/-- Off the locus `b = 0`, every point other than `p` and `q` has coefficient
`0`. -/
theorem family_coeff_eq_zero_of_ne (k : Type u) [Field k] (s : base k)
    (h : evalY k s ≠ 0) {x : (hom k).fiber s}
    (hxP : x ≠ pointP k s h) (hxQ : x ≠ pointQ k s h) :
    CyclesOnFibers.toAlgebraicCycle (family k) s x = 0 :=
  by
    classical
    simp [CyclesOnFibers.toAlgebraicCycle, family, h, CycleGroup.toAlgebraicCycle,
      CycleGroup.point, hxP, hxQ]

/-- The family of zero-cycles is compatible with specializations and hence is
a relative zero-cycle. -/
theorem family_isRelative (k : Type u) [Field k] :
    RelativeCycle.IsRelative (family k) :=
  sorry

/-- The closure of the support of the family contains the whole fibre over
the origin of the affine plane. -/
theorem closure_support_contains_originFiber (k : Type u) [Field k] :
    Set.range ((hom k).fiberι (origin k)) ⊆
      closure (CyclesOnFibers.support (family k)) :=
  sorry

/-- The family is not equidimensional: its support is not contained in a
closed subscheme of relative dimension at most zero over the affine plane. -/
theorem not_equidimensional (k : Type u) [Field k] :
    ¬ Equidimensional (family k) :=
  sorry

end AlgebraicGeometry.AffineLineOverPlane
