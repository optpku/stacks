module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Induced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SelfFibreProduct

/-!
# Smooth pointed scheme charts of algebraic stacks

A smooth scheme chart records a finite type point over a stack point and a
representation of the self 2-fibre product with its canonical diagonal.
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

/-- A finite type point of an algebraic stack admits a smooth scheme chart. -/
theorem exists_smoothSchemeChart {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} (hx : IsFiniteTypePoint x) :
    Nonempty (SmoothSchemeChart x) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
