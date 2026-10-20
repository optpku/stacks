/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothChart
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.LocalRing

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end AlgebraicGeometry.AlgebraicStack
