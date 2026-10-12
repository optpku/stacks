/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.CardComponents
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Lemma_68_18_6_Fibre

/-!
# Numbers of geometric connected components of fibres of algebraic spaces

The extended-natural-valued function `geometricFiberComponentCount f` counts
connected components of geometric fibres of a morphism of algebraic spaces. It
is independent of the algebraically closed representative of a point of `|Y|`
and is invariant under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace GeometricPoint

/-- The geometric point obtained by extending a field-valued point along the
algebraic closure of its source field. -/
noncomputable def extend {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : FieldValuedPoint X) : GeometricPoint X :=
  let f := AlgebraicGeometry.FieldExtension.specMap p.K (AlgebraicClosure p.K)
  of (AlgebraicClosure p.K) (f ≫ p.structureHom) (ofOverHomMk f rfl ≫ p.hom)

/-- The algebraic-closure extension of a field-valued point has image the class
of that point. -/
theorem extend_image {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : FieldValuedPoint X) : (extend p).image = Points.mk p :=
  sorry

end GeometricPoint

/-- A chosen geometric point of `Y` lying over `y`, obtained by algebraic closure
of a field-valued representative. -/
noncomputable def geometricPointOver {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (y : Points Y) : GeometricPoint Y :=
  GeometricPoint.extend (Quotient.out (y : Quotient (equivalentSetoid Y)))

/-- The chosen geometric point over `y` has image `y`. -/
theorem geometricPointOver_image {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (y : Points Y) : (geometricPointOver y).image = y :=
  sorry

/-- The number of connected components of the geometric fibre of `f` at a
geometric point of the target. -/
noncomputable def geometricFiberComponentCountAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y) : ℕ∞ :=
  ENat.card (ConnectedComponents (Points (fieldFiber f ybar.toFieldValuedPoint)))

/-- The geometric fibre-component count at a geometric point depends only on the
image of that geometric point in `|Y|`. -/
theorem geometricFiberComponentCountAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ybar zbar : GeometricPoint Y) (h : ybar.image = zbar.image) :
    geometricFiberComponentCountAt f ybar = geometricFiberComponentCountAt f zbar :=
  sorry

/-- The function sending a point of `|Y|` to the number of connected components
of a geometric fibre of `f` over an algebraically closed representative of that
point. -/
noncomputable def geometricFiberComponentCount {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Points Y → ℕ∞ :=
  fun y ↦ geometricFiberComponentCountAt f (geometricPointOver y)

/-- Evaluating `geometricFiberComponentCount f` at `y` is the geometric
fibre-component count at the chosen geometric point over `y`. -/
theorem geometricFiberComponentCount_apply {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    geometricFiberComponentCount f y =
      geometricFiberComponentCountAt f (geometricPointOver y) :=
  sorry

/-- The value of `geometricFiberComponentCount f` at `y` equals the number of
connected components of the fibre over any algebraically closed representative
of `y`. -/
theorem geometricFiberComponentCount_eq_enatCard {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) (ybar : GeometricPoint Y)
    (hy : ybar.image = y) :
    geometricFiberComponentCount f y =
      ENat.card
        (ConnectedComponents (Points (fieldFiber f ybar.toFieldValuedPoint))) :=
  sorry

/-- The geometric fibre-component count of a morphism of algebraic spaces is
invariant under arbitrary base change. -/
theorem geometricFiberComponentCount_baseChange {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) :
    geometricFiberComponentCount f' =
      geometricFiberComponentCount f ∘ Points.map g :=
  sorry

/-- Evaluating the base-changed geometric fibre-component count at `y'` recovers
the original count at the image of `y'`. -/
theorem geometricFiberComponentCount_baseChange_apply {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) (y' : Points Y') :
    geometricFiberComponentCount f' y' =
      geometricFiberComponentCount f (Points.map g y') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

