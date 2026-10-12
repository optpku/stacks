/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.PointwiseRegular
import StacksCheckRecall

@[expose] public section

/-!
# Definition 33.12.1 compatibility entry point

The field-extension stalkwise API for geometrically regular locally Noetherian
schemes is owned by
`ReasLib.AlgebraicGeometry.Scheme.Geometrically.PointwiseRegular`.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Definition 33.12.1 (1): a locally Noetherian scheme over a field is geometrically regular
at a point when every point above it after every essentially finite-type field extension has
a regular local ring. -/
@[stacks 038T] #check
  (AlgebraicGeometry.Scheme.Hom.isGeometricallyRegularAt_iff :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) {x : X} [IsLocallyNoetherian X],
      AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegularAt f x ↔
        ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
          ∀ x' : FieldExtension.baseChange k K f,
            FieldExtension.toSource k K f x' = x →
              IsRegularLocalRing ((FieldExtension.baseChange k K f).presheaf.stalk x'))

/- Definition 33.12.1 (2): a locally Noetherian scheme over a field is geometrically regular
when it is geometrically regular at every point. -/
@[stacks 038T] #check
  (AlgebraicGeometry.Scheme.Hom.isGeometricallyRegular_iff :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsLocallyNoetherian X],
      AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegular f ↔
        ∀ x : X, AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegularAt f x)
