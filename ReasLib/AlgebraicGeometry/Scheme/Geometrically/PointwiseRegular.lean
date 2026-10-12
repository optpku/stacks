/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.EssentialFiniteness
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stalk
public import ReasLib.FieldTheory.GeometricRegularity

/-!
# Geometrically regular schemes at points

This leaf records the stalkwise finite-type field-extension formulation of
geometric regularity for locally Noetherian schemes over a field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A scheme morphism to the spectrum of a field is geometrically regular at `x` when every
point above `x` after every essentially finite-type field extension has a regular local ring. -/
class IsGeometricallyRegularAt (f : X ⟶ Spec (CommRingCat.of k)) (x : X) : Prop where
  /-- Every essentially finite-type field-extension base-change point above `x` has a regular
  local ring. -/
  isRegularLocalRing_stalk :
    ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
      ∀ x' : FieldExtension.baseChange k K f,
        FieldExtension.toSource k K f x' = x →
          IsRegularLocalRing ((FieldExtension.baseChange k K f).presheaf.stalk x')

/-- For a locally Noetherian scheme, geometric regularity at a point is equivalent to the
regular-stalk condition after every essentially finite-type field extension. -/
@[stacks 038T]
theorem isGeometricallyRegularAt_iff {x : X} [IsLocallyNoetherian X] :
    IsGeometricallyRegularAt f x ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
        ∀ x' : FieldExtension.baseChange k K f,
          FieldExtension.toSource k K f x' = x →
            IsRegularLocalRing ((FieldExtension.baseChange k K f).presheaf.stalk x') := sorry

namespace IsGeometricallyRegularAt

/-- For a locally Noetherian scheme, geometric regularity at `x` can be tested after every
finite purely inseparable extension of the ground field and at every point above `x`. -/
@[stacks 038U]
theorem iff_forall_regularStalk_finitePurelyInseparable
    {x : X} [IsLocallyNoetherian X] :
    IsGeometricallyRegularAt f x ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
        [IsPurelyInseparable k K],
        ∀ x' : FieldExtension.baseChange k K f,
          FieldExtension.toSource k K f x' = x →
            IsRegularLocalRing ((FieldExtension.baseChange k K f).presheaf.stalk x') := sorry

/-- For a locally Noetherian scheme, geometric regularity at `x` is equivalent to geometric
regularity of its stalk algebra over the ground field. -/
@[stacks 038U]
theorem iff_stalk_geometricallyRegular {x : X} [IsLocallyNoetherian X] :
    IsGeometricallyRegularAt f x ↔
      Algebra.IsGeometricallyRegular k (stalkAlgOverField f x) := sorry

end IsGeometricallyRegularAt

/-- A scheme morphism to the spectrum of a field is geometrically regular when it is
geometrically regular at every point of its source. -/
class IsGeometricallyRegular (f : X ⟶ Spec (CommRingCat.of k)) : Prop where
  /-- Geometric regularity holds at every point of the source scheme. -/
  isGeometricallyRegularAt : ∀ x : X, IsGeometricallyRegularAt f x

/-- A geometrically regular scheme is geometrically regular at each point. -/
instance instIsGeometricallyRegularAt (x : X) [h : IsGeometricallyRegular f] :
    IsGeometricallyRegularAt f x :=
  h.isGeometricallyRegularAt x

/-- For a locally Noetherian scheme, geometric regularity is equivalent to geometric
regularity at every point. -/
@[stacks 038T]
theorem isGeometricallyRegular_iff [IsLocallyNoetherian X] :
    IsGeometricallyRegular f ↔ ∀ x : X, IsGeometricallyRegularAt f x := sorry

end AlgebraicGeometry.Scheme.Hom
