module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-!
# Relative dimension of a space-to-stack morphism at a point

For a locally of finite type morphism from an algebraic space `T` to an
algebraic stack `X`, the relative dimension `dim_t(T_x)` is the dimension of
an algebraic-space model of the 2-fibre `T ×_X Spec k` at a lift of `t`. The
numeric value is the supremum of those fibre dimensions over representing
choices.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Noncanonical data for computing `dim_t(T_x)`: a field-valued representative
of the image of `t`, an algebraic-space model of `T ×_X Spec k`, and a lift of
`t` to that fibre. -/
structure RelativeDimensionChoice {S : Scheme.{u}} {T : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : T.toGroupoids ⟶ X)
    (t : AlgebraicSpace.Points T) where
  /-- A field-valued point of `X` representing the image of `t`. -/
  point : FieldValuedPoint X
  /-- An algebraic-space model of the 2-fibre product `T ×_X Spec k`. -/
  fiber : AlgebraicSpace S
  /-- Equivalence of the 2-fibre product apex with the algebraic-space model. -/
  apexEquiv :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} point.hom f ≌ fiber.toGroupoids
  /-- A lift of `t` to a point of the fibre space. -/
  fiberPoint : AlgebraicSpace.Points fiber
  /-- `point` represents the image of `t` in `|X|`. -/
  representsImage : Points.mk point = Points.map f (Points.ofAlgebraicSpace t)
  /-- The fibre point maps to `t` under the projection to `T`. -/
  mapsToSource :
    AlgebraicSpace.Points.map
      (AlgebraicSpace.toGroupoids.eval
        (apexEquiv.inv ≫
          TwoFibreProduct.snd.{u + 1, u, u + 1, u} point.hom f))
      fiberPoint = t

namespace RelativeDimensionChoice

variable {S : Scheme.{u}} {T : AlgebraicSpace S} {X : GroupoidsOver S}
variable [AlgebraicStack X] {f : T.toGroupoids ⟶ X} {t : AlgebraicSpace.Points T}

/-- The projection `T ×_X Spec k ⟶ T` recovered from an algebraic-space model
of the 2-fibre product. -/
def projection (w : RelativeDimensionChoice f t) : w.fiber ⟶ T :=
  AlgebraicSpace.toGroupoids.eval
    (w.apexEquiv.inv ≫
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} w.point.hom f)

/-- The fibre point of a relative-dimension choice maps to `t` along the
projection to the source. -/
theorem projection_spec (w : RelativeDimensionChoice f t) :
    AlgebraicSpace.Points.map w.projection w.fiberPoint = t :=
  sorry

/-- The dimension of the representing fibre at its chosen point. -/
def dimension (w : RelativeDimensionChoice f t) : WithBot ℕ∞ :=
  AlgebraicSpace.dimensionAt w.fiberPoint

/-- The dimension of a relative-dimension choice is the algebraic-space
dimension at the chosen fibre point. -/
theorem dimension_def (w : RelativeDimensionChoice f t) :
    w.dimension = AlgebraicSpace.dimensionAt w.fiberPoint :=
  sorry

/-- A relative-dimension choice represents the image of `t` and lifts `t` along
the fibre projection. -/
theorem spec (w : RelativeDimensionChoice f t) :
    Points.mk w.point = Points.map f (Points.ofAlgebraicSpace t) ∧
      AlgebraicSpace.Points.map w.projection w.fiberPoint = t :=
  sorry

end RelativeDimensionChoice

/-- The relative dimension `dim_t(T_x)` of a locally of finite type morphism
from an algebraic space to an algebraic stack, as the supremum of
`AlgebraicSpace.dimensionAt` along representing fibres. -/
noncomputable def fiberDimensionAt {S : Scheme.{u}} {T : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : T.toGroupoids ⟶ X)
    [LocallyOfFiniteType f] (t : AlgebraicSpace.Points T) : WithBot ℕ∞ :=
  ⨆ w : RelativeDimensionChoice f t, w.dimension

/-- The dimensions at any two representing fibres of a locally-of-finite-type
morphism from an algebraic space to an algebraic stack are equal. -/
theorem fiberDimensionAt_independent {S : Scheme.{u}} {T : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : T.toGroupoids ⟶ X)
    [LocallyOfFiniteType f] (t : AlgebraicSpace.Points T)
    (w w' : RelativeDimensionChoice f t) : w.dimension = w'.dimension :=
  sorry

/-- The relative dimension at `t` equals the fibre dimension of any
representing choice. -/
theorem fiberDimensionAt_eq {S : Scheme.{u}} {T : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : T.toGroupoids ⟶ X)
    [LocallyOfFiniteType f] (t : AlgebraicSpace.Points T)
    (w : RelativeDimensionChoice f t) :
    fiberDimensionAt f t = w.dimension :=
  sorry

/-- A representing fibre and a lift of `t` exist, by the surjectivity of points
of a 2-fibre product. -/
theorem exists_relativeDimensionChoice {S : Scheme.{u}} {T : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : T.toGroupoids ⟶ X)
    (t : AlgebraicSpace.Points T) : Nonempty (RelativeDimensionChoice f t) :=
  sorry

/-- For a locally-of-finite-type morphism of algebraic spaces, the dimension
at any representing fibre equals the algebraic-space fibre dimension. -/
theorem fiberDimensionAt_eq_of_algebraicSpace {S : Scheme.{u}}
    {T Y : AlgebraicSpace S} (φ : T ⟶ Y) [AlgebraicSpace.LocallyOfFiniteType φ]
    (t : AlgebraicSpace.Points T)
    (w : RelativeDimensionChoice (AlgebraicSpace.toGroupoids.map φ) t) :
    w.dimension = AlgebraicSpace.fiberDimensionAt φ t :=
  sorry

/-- For an algebraic-space target, exact relative dimension `d` is equivalent
to the space-to-stack fibre dimension being `d`. -/
theorem fiberDimensionAt_iff_relativeDimensionAt {S : Scheme.{u}}
    {T Y : AlgebraicSpace S} (φ : T ⟶ Y) [AlgebraicSpace.LocallyOfFiniteType φ]
    (d : ℕ) (t : AlgebraicSpace.Points T) :
    AlgebraicSpace.RelativeDimensionAt φ d t ↔
      fiberDimensionAt (AlgebraicSpace.toGroupoids.map φ) t =
        (d : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
