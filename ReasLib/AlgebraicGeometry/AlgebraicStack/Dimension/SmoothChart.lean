/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothChart
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Smooth
public import ReasLib.RingTheory.Henselian.Henselization.KrullDimension
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Local-ring dimension differences of smooth scheme charts

The extended-integer difference of twice the source local-ring dimension and
the self 2-fibre-product local-ring dimension is independent of the smooth
scheme chart over a finite type point of a locally Noetherian algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The local-ring dimension difference `2 dim 𝒪_{U, u} - dim 𝒪_{R, e(u)}`, as
an extended integer built from `AlgebraicSpace.localRingDimAt`. -/
noncomputable def localRingDimDiff {S : Scheme.{u}} {U : Over S} {R : AlgebraicSpace S}
    (e : AlgebraicSpace.ofOver U ⟶ R) (u : U.left) : EInt :=
  let dU := AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u)
  let dR := AlgebraicSpace.localRingDimAt
    (AlgebraicSpace.Points.map e (AlgebraicSpace.ofOver.pointsEquiv U u))
  dimensionDiff (dU + dU) dR

/-- `localRingDimDiff` is `dimensionDiff` of twice the local-ring dimension of
`U` at `u` with the local-ring dimension of `R` at `e(u)`. -/
theorem localRingDimDiff_eq {S : Scheme.{u}} {U : Over S} {R : AlgebraicSpace S}
    (e : AlgebraicSpace.ofOver U ⟶ R) (u : U.left) :
    localRingDimDiff e u =
      dimensionDiff
        (AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u) +
          AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u))
        (AlgebraicSpace.localRingDimAt
          (AlgebraicSpace.Points.map e (AlgebraicSpace.ofOver.pointsEquiv U u))) :=
  rfl

/-- The local-ring dimension difference equals the étale-local-ring form
`dimensionDiff (dim 𝒪_{U, ū} + dim 𝒪_{U, ū}) (dim 𝒪_{R, e(ū)})`. -/
theorem localRingDimDiff_etale {S : Scheme.{u}} {U : Over S} {R : AlgebraicSpace S}
    (e : AlgebraicSpace.ofOver U ⟶ R) (u : U.left)
    (ubar : Scheme.GeometricPoint U.left) (hu : ubar.image = u) :
    localRingDimDiff e u =
      dimensionDiff
        (ringKrullDim (Scheme.etaleLocalRing U.left ubar) +
          ringKrullDim (Scheme.etaleLocalRing U.left ubar))
        (ringKrullDim
          (AlgebraicSpace.etaleLocalRing R
            ((AlgebraicSpace.GeometricPoint.ofScheme ubar).map e))) :=
  by
    have hU :
        AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u) =
          ringKrullDim (Scheme.etaleLocalRing U.left ubar) := by
      rw [AlgebraicSpace.localRingDimAt_ofOver, ← hu]
      exact IsStrictHenselizationOf.ringKrullDim_eq
        (R := U.left.presheaf.stalk ubar.image)
        (S := Scheme.etaleLocalRing U.left ubar)
    have hR :
        ringKrullDim
            (AlgebraicSpace.etaleLocalRing R
              ((AlgebraicSpace.GeometricPoint.ofScheme ubar).map e)) =
          AlgebraicSpace.localRingDimAt
            (AlgebraicSpace.Points.map e (AlgebraicSpace.ofOver.pointsEquiv U u)) := by
      rw [AlgebraicSpace.ringKrullDim_etaleLocalRing_eq,
        AlgebraicSpace.GeometricPoint.map_image,
        AlgebraicSpace.GeometricPoint.ofScheme_image, hu]
    rw [localRingDimDiff_eq, hU, hR]

/-- By the self-fibre identity, `localRingDimDiff` equals
`dimensionDiff` of the local-ring dimension of `U` at `u` with the fibre
stalk dimension of `s` at `e(u)`. -/
theorem localRingDimDiff_fiber {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    {R : AlgebraicSpace S} (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) (hR : IsSelfFibreProduct p s t e)
    (u : U.left) :
    localRingDimDiff e u =
      dimensionDiff
        (AlgebraicSpace.localRingDimAt (AlgebraicSpace.ofOver.pointsEquiv U u))
        (AlgebraicSpace.fiberStalkDimAt s
          (AlgebraicSpace.Points.map e (AlgebraicSpace.ofOver.pointsEquiv U u))) :=
  (smoothSelfFibre_localRingDimAt_eq p s t e hR u).symm

namespace SmoothSchemeChart

/-- The local-ring dimension difference of a smooth scheme chart. -/
noncomputable def localRingDimDiff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (c : SmoothSchemeChart x) : EInt :=
  AlgebraicGeometry.AlgebraicStack.localRingDimDiff c.e c.u

/-- For a finite type point of a locally Noetherian algebraic stack, the
local-ring dimension difference is independent of the smooth scheme chart. -/
theorem localRingDimDiff_independent {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {x : Points X}
    (hx : IsFiniteTypePoint x) (c₁ c₂ : SmoothSchemeChart x) :
    c₁.localRingDimDiff = c₂.localRingDimDiff :=
  sorry

/-- The local-ring dimension difference of a chart through a finite type point
is an ordinary integer. -/
theorem localRingDimDiff_eq_int {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {x : Points X}
    (hx : IsFiniteTypePoint x) (c : SmoothSchemeChart x) :
    ∃ n : ℤ, c.localRingDimDiff = n :=
  by
    letI : AlgebraicGeometry.IsLocallyNoetherian c.U.left :=
      (existsSurjectiveSmooth_iff_forallSmooth
        (AlgebraicGeometry.IsLocallyNoetherian : ObjectProperty Scheme.{u}) X).mp
        (inferInstance : IsLocallyNoetherian X).exists_locallyNoetherian_smooth_cover
        c.U c.hom c.smooth
    letI : AlgebraicSpace.Smooth c.s :=
      c.smooth.of_represents c.hom c.R c.s c.isSelfFibreProduct.representsBaseChange
    letI : AlgebraicSpace.IsLocallyNoetherian c.R :=
      AlgebraicSpace.LocallyOfFiniteType.isLocallyNoetherian c.s
    have hfinite : ∀ {F : AlgebraicSpace S} [AlgebraicSpace.IsLocallyNoetherian F]
        (y : AlgebraicSpace.Points F),
        ∃ n : ℕ, AlgebraicSpace.localRingDimAt y = n := by
      intro F hF y
      obtain ⟨ybar, _, hybar⟩ :=
        (AlgebraicSpace.localRingDimAt_eq_iff_exists_etaleLocalRing y
          (AlgebraicSpace.localRingDimAt y)).mp rfl
      letI := AlgebraicSpace.etaleLocalRing.instIsNoetherianRing ybar
      letI := AlgebraicSpace.etaleLocalRing.instIsLocalRing ybar
      have hbot := ringKrullDim_ne_bot (R := AlgebraicSpace.etaleLocalRing F ybar)
      have htop := ringKrullDim_ne_top (R := AlgebraicSpace.etaleLocalRing F ybar)
      rcases hdim : ringKrullDim (AlgebraicSpace.etaleLocalRing F ybar) with _ | (_ | n)
      · exact (hbot hdim).elim
      · exact (htop hdim).elim
      · exact ⟨n, hybar.symm.trans hdim⟩
    obtain ⟨n, hn⟩ := hfinite (AlgebraicSpace.ofOver.pointsEquiv c.U c.u)
    obtain ⟨m, hm⟩ := hfinite
      (AlgebraicSpace.Points.map c.e (AlgebraicSpace.ofOver.pointsEquiv c.U c.u))
    refine ⟨(n : ℤ) + n - m, ?_⟩
    change AlgebraicStack.localRingDimDiff c.e c.u = _
    rw [AlgebraicStack.localRingDimDiff_eq, hn, hm, ← Nat.cast_add,
      dimensionDiff_nat, Nat.cast_add]

end SmoothSchemeChart

/-- For a finite type point of a locally Noetherian algebraic stack and an
integer `d`, the local-ring dimension difference equals `d` on some smooth
scheme chart if and only if it equals `d` on every smooth scheme chart. -/
@[stacks 0DS9]
theorem exists_localRingDimDiff_eq_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {x : Points X}
    (hx : IsFiniteTypePoint x) (d : ℤ) :
    (∃ c : SmoothSchemeChart x, c.localRingDimDiff = d) ↔
      ∀ c : SmoothSchemeChart x, c.localRingDimDiff = d :=
  by
    constructor
    · rintro ⟨c, hc⟩ c'
      exact (SmoothSchemeChart.localRingDimDiff_independent hx c' c).trans hc
    · intro h
      obtain ⟨c⟩ := exists_smoothSchemeChart hx
      exact ⟨c, h c⟩

/-- For a finite type point of a locally Noetherian algebraic stack, the
existence of a smooth scheme neighbourhood with local-ring dimension
difference `d` is equivalent to that equality for every such neighbourhood,
quantifying explicitly over schemes, self 2-fibre products, and points. -/
theorem exists_localRingDimDiff_eq_unbundled_iff {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {x : Points X} (hx : IsFiniteTypePoint x) (d : ℤ) :
    (∃ (U : Over S) (hom : GroupoidsOver.slice U ⟶ X) (R : AlgebraicSpace S)
        (s t : R ⟶ AlgebraicSpace.ofOver U) (e : AlgebraicSpace.ofOver U ⟶ R)
        (u : U.left),
      Groupoids.Hom.Smooth hom ∧ IsSelfFibreProduct hom s t e ∧
        AlgebraicGeometry.IsFiniteTypePoint u ∧ Points.mapSlice hom u = x ∧
          localRingDimDiff e u = d) ↔
      ∀ (U : Over S) (hom : GroupoidsOver.slice U ⟶ X) (R : AlgebraicSpace S)
        (s t : R ⟶ AlgebraicSpace.ofOver U) (e : AlgebraicSpace.ofOver U ⟶ R)
        (u : U.left),
        Groupoids.Hom.Smooth hom → IsSelfFibreProduct hom s t e →
          AlgebraicGeometry.IsFiniteTypePoint u → Points.mapSlice hom u = x →
            localRingDimDiff e u = d :=
  by
    constructor
    · rintro ⟨U, hom, R, s, t, e, u, hsm, hR, hu, hux, hd⟩
      letI := hsm
      have hc : ∃ c : SmoothSchemeChart x, c.localRingDimDiff = d :=
        ⟨SmoothSchemeChart.of hom s t e hR u hu hux, hd⟩
      intro U' hom' R' s' t' e' u' hsm' hR' hu' hux'
      letI := hsm'
      exact (exists_localRingDimDiff_eq_iff hx d).mp hc
        (SmoothSchemeChart.of hom' s' t' e' hR' u' hu' hux')
    · intro h
      obtain ⟨c⟩ := exists_smoothSchemeChart hx
      exact ⟨c.U, c.hom, c.R, c.s, c.t, c.e, c.u, c.smooth,
        c.isSelfFibreProduct, c.isFiniteTypePoint, c.mapsTo,
        h c.U c.hom c.R c.s c.t c.e c.u c.smooth c.isSelfFibreProduct
          c.isFiniteTypePoint c.mapsTo⟩

end AlgebraicGeometry.AlgebraicStack
