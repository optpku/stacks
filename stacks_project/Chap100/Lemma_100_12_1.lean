module

public import stacks_project.Chap100.Definition_100_12_3_Dimension

/-!
# Independence of presentation differences at a point

For a locally Noetherian algebraic stack, the difference
`dim_u(U) - dim_{e(u)}(R_u)` attached to a presentation through a point of `|X|`
is independent of the presentation and of the chosen point over `x`, and takes
values in `ℤ ∪ {∞}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Presentation

/-- The presentation difference `AlgebraicSpace.dimensionAt` at a point of the
object space minus `AlgebraicSpace.fiberDimensionAt` of the source map at the
identity arrow of that point. -/
noncomputable def dimensionDiffAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left) : EInt :=
  dimensionDiff (AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.mk p))
    (AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
      (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p)))

/-- Unfolding of `Presentation.dimensionDiffAt` as `dimensionDiff` of the object-space
dimension and the fibre dimension of the source map at the identity arrow. -/
theorem dimensionDiffAt_def {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left) :
    P.dimensionDiffAt p =
      dimensionDiff (AlgebraicSpace.dimensionAt (AlgebraicSpace.Points.mk p))
        (AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
          (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p))) :=
  sorry

/-- Lemma 100.12.1 (1): let `X` be a locally Noetherian algebraic stack over a scheme
`S`, and let `x` be a point of `|X|`. If `P` and `P'` are presentations `[U/R] ⟶ X`
and `[U'/R'] ⟶ X` (Algebraic Stacks, Definition 94.16.5) with object spaces schemes,
and if `p`, `p'` are points of those object spaces mapping to `x`, then
`P.dimensionDiffAt p = P'.dimensionDiffAt p'`. Here `e` is the identity map of the
presenting groupoid, `s` is the source map (smooth as a morphism of algebraic
spaces), and the displayed difference is `AlgebraicSpace.dimensionAt` at `u` minus
`AlgebraicSpace.fiberDimensionAt s` at `e(u)`, for `R_u` the fibre of `s` over `u`. -/
@[stacks 0AFM]
theorem dimensionDiffAt_independent {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    (P P' : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left)
    (p' : AlgebraicSpace.FieldValuedPoint P'.groupoid.U.left)
    (hp : Points.map (P.groupoid.atlas ≫ P.hom)
      (Points.mk (FieldValuedPoint.ofAlgebraicSpace p)) = x)
    (hp' : Points.map (P'.groupoid.atlas ≫ P'.hom)
      (Points.mk (FieldValuedPoint.ofAlgebraicSpace p')) = x) :
    P.dimensionDiffAt p = P'.dimensionDiffAt p' :=
  sorry

/-- Lemma 100.12.1 (2): let `X` be a locally Noetherian algebraic stack over a scheme
`S`, let `x` be a point of `|X|`, and let `P` be a presentation `[U/R] ⟶ X`
(Algebraic Stacks, Definition 94.16.5) with object space a scheme and a point `p`
of that object space mapping to `x`. Then `P.dimensionDiffAt p` lies in
`ℤ ∪ {∞}`, i.e. equals `⊤` or an integer in `EInt`. Smoothness of the source map
`s` makes `AlgebraicSpace.fiberDimensionAt s` at `e(u)` finite, while
`AlgebraicSpace.dimensionAt` at `u` may be infinite, so the value cannot be `⊥`. -/
@[stacks 0AFM]
theorem dimensionDiffAt_eq_top_or_int {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left)
    (hp : Points.map (P.groupoid.atlas ≫ P.hom)
      (Points.mk (FieldValuedPoint.ofAlgebraicSpace p)) = x) :
    P.dimensionDiffAt p = ⊤ ∨ ∃ n : ℤ, P.dimensionDiffAt p = n :=
  sorry

/-- The fibre of the source map of a presentation at the identity arrow of a point of
the object space has finite dimension. -/
theorem fiberDimensionAt_identity_eq_nat {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (P : Presentation X)
    (p : AlgebraicSpace.FieldValuedPoint P.groupoid.U.left) :
    ∃ n : ℕ,
      AlgebraicSpace.fiberDimensionAt P.groupoid.s.left
          (AlgebraicSpace.Points.map P.groupoid.e.left (AlgebraicSpace.Points.mk p)) =
        n :=
  sorry

end Presentation

end AlgebraicGeometry.AlgebraicStack
