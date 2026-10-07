module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.PointwiseRegular

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/-!
# Lemma 33.12.2 canonical recall

The reusable pointwise criteria are owned by
`AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegularAt`.
-/

/- Lemma 33.12.2 (1): geometric regularity at a point is equivalent to regularity of every
stalk above it after every finite purely inseparable extension of the ground field. -/
@[stacks 038U] #check
  (AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegularAt.iff_forall_regularStalk_finitePurelyInseparable :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) {x : X} [IsLocallyNoetherian X],
      Scheme.Hom.IsGeometricallyRegularAt f x ↔
        ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
          [IsPurelyInseparable k K],
          ∀ x' : FieldExtension.baseChange k K f,
            FieldExtension.toSource k K f x' = x →
              IsRegularLocalRing ((FieldExtension.baseChange k K f).presheaf.stalk x'))

/- Lemma 33.12.2 (2): geometric regularity at a point is equivalent to geometric regularity
over the ground field of the canonical stalk algebra. -/
@[stacks 038U] #check
  (AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegularAt.iff_stalk_geometricallyRegular :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) {x : X} [IsLocallyNoetherian X],
      Scheme.Hom.IsGeometricallyRegularAt f x ↔
        Algebra.IsGeometricallyRegular k (Scheme.Hom.stalkAlgOverField f x))
