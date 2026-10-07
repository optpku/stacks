module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap67.Lemma_67_34_3_FiberDimension
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap100.Lemma_100_4_3_Comparison
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

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

namespace FieldValuedPoint.Equivalent

/-- Equivalence of field-valued points of an algebraic space is preserved by
passage to the associated algebraic stack. -/
theorem ofAlgebraicSpace {S : Scheme.{u}} {F : AlgebraicSpace S}
    {p q : AlgebraicSpace.FieldValuedPoint F}
    (h : AlgebraicSpace.FieldValuedPoint.Equivalent p q) :
    Equivalent (FieldValuedPoint.ofAlgebraicSpace p)
      (FieldValuedPoint.ofAlgebraicSpace q) :=
  sorry

end FieldValuedPoint.Equivalent

namespace Points

/-- The image in `|T.toGroupoids|` of a point of an algebraic space `T`. -/
noncomputable def ofAlgebraicSpace {S : Scheme.{u}} {F : AlgebraicSpace S}
    (x : AlgebraicSpace.Points F) : Points F.toGroupoids :=
  Quotient.map (fun p : AlgebraicSpace.FieldValuedPoint F ↦
      FieldValuedPoint.ofAlgebraicSpace p)
    (fun _ _ h ↦ FieldValuedPoint.Equivalent.ofAlgebraicSpace h) x

/-- Passage to stack points sends the class of a field-valued point to the class
of its associated field-valued point of `T.toGroupoids`. -/
theorem ofAlgebraicSpace_mk {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) :
    ofAlgebraicSpace (AlgebraicSpace.Points.mk p) =
      mk (FieldValuedPoint.ofAlgebraicSpace p) :=
  sorry

end Points

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

/-- Pack representing-fibre data for `dim_t(T_x)` into a relative-dimension
choice. -/
def of (point : FieldValuedPoint X) (fiber : AlgebraicSpace S)
    (apexEquiv :
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} point.hom f ≌ fiber.toGroupoids)
    (fiberPoint : AlgebraicSpace.Points fiber)
    (representsImage : Points.mk point = Points.map f (Points.ofAlgebraicSpace t))
    (mapsToSource :
      AlgebraicSpace.Points.map
        (AlgebraicSpace.toGroupoids.eval
          (apexEquiv.inv ≫
            TwoFibreProduct.snd.{u + 1, u, u + 1, u} point.hom f))
        fiberPoint = t) :
    RelativeDimensionChoice f t where
  point := point
  fiber := fiber
  apexEquiv := apexEquiv
  fiberPoint := fiberPoint
  representsImage := representsImage
  mapsToSource := mapsToSource

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

/-- The source formula `dim_{t'}(T ×_X Spec k)` associated to a representing
fibre. -/
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

/-- When the target is an algebraic space, exact relative dimension `d` in the
sense of Morphisms of Spaces Definition 67.33.1 is equality of the space-to-stack
relative dimension with `d`. -/
theorem fiberDimensionAt_iff_relativeDimensionAt {S : Scheme.{u}}
    {T Y : AlgebraicSpace S} (φ : T ⟶ Y) [AlgebraicSpace.LocallyOfFiniteType φ]
    (d : ℕ) (t : AlgebraicSpace.Points T) :
    AlgebraicSpace.RelativeDimensionAt φ d t ↔
      fiberDimensionAt (AlgebraicSpace.toGroupoids.map φ) t =
        (d : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
