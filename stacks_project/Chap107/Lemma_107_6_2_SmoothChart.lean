/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import stacks_project.Chap101.Lemma_101_18_4_FiniteTypePoint
public import stacks_project.Chap107.Lemma_107_6_1

/-!
# Smooth scheme charts and the local-ring dimension difference

A smooth neighbourhood of a point of an algebraic stack is a scheme morphism
to the stack together with a representing self 2-fibre product. The associated
local-ring quantity is `2 dim 𝒪_{U, u} - dim 𝒪_{R, e(u)}`, valued in `EInt`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A smooth scheme neighbourhood of a point `x` of an algebraic stack, with a
representing self 2-fibre product `R` of the chart morphism. -/
structure SmoothSchemeChart {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (x : Points X) where
  /-- The source scheme over `S`. -/
  U : Over S
  /-- The 1-morphism from the slice of `U` to `X`. -/
  hom : GroupoidsOver.slice U ⟶ X
  /-- An algebraic space representing the self 2-fibre product of `hom`. -/
  R : AlgebraicSpace S
  /-- The source projection `R ⟶ U`. -/
  s : R ⟶ AlgebraicSpace.ofOver U
  /-- The target projection `R ⟶ U`. -/
  t : R ⟶ AlgebraicSpace.ofOver U
  /-- The diagonal section `U ⟶ R`. -/
  e : AlgebraicSpace.ofOver U ⟶ R
  /-- A point of `U` mapping to `x`. -/
  u : U.left
  /-- The chart morphism is smooth. -/
  smooth : Groupoids.Hom.Smooth hom
  /-- `R` represents the self 2-fibre product of `hom`, identifying `s`, `t`,
  and `e` with the two projections and the diagonal. -/
  isSelfFibreProduct : IsSelfFibreProduct hom s t e
  /-- The chart point `u` is a finite type point of `U`. -/
  isFiniteTypePoint : AlgebraicGeometry.IsFiniteTypePoint u
  /-- The image of `u` in `|X|` is `x`. -/
  mapsTo : Points.mapSlice hom u = x

namespace SmoothSchemeChart

/-- Pack a smooth scheme morphism, a representing self 2-fibre product, and a
finite type point mapping to `x` into a chart. -/
def of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X}
    {U : Over S} (hom : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth hom]
    {R : AlgebraicSpace S} (s t : R ⟶ AlgebraicSpace.ofOver U)
    (e : AlgebraicSpace.ofOver U ⟶ R) (hR : IsSelfFibreProduct hom s t e)
    (u : U.left) (hu : AlgebraicGeometry.IsFiniteTypePoint u)
    (hx : Points.mapSlice hom u = x) : SmoothSchemeChart x where
  U := U
  hom := hom
  R := R
  s := s
  t := t
  e := e
  u := u
  smooth := inferInstance
  isSelfFibreProduct := hR
  isFiniteTypePoint := hu
  mapsTo := hx

/-- A smooth scheme chart is a smooth morphism from a scheme together with a
representing self 2-fibre product and a finite type point mapping to `x`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (c : SmoothSchemeChart x) :
    Groupoids.Hom.Smooth c.hom ∧ IsSelfFibreProduct c.hom c.s c.t c.e ∧
      AlgebraicGeometry.IsFiniteTypePoint c.u ∧ Points.mapSlice c.hom c.u = x :=
  sorry

end SmoothSchemeChart

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

/-- A finite type point of an algebraic stack admits a smooth scheme chart. -/
theorem exists_smoothSchemeChart {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (hx : IsFiniteTypePoint x) :
    Nonempty (SmoothSchemeChart x) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
