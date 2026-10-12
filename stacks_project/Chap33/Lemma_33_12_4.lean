/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Regular.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 33.12.4 (1): geometric regularity at a point is invariant under a finitely generated
field extension at a point of the base change lying over it. -/
@[stacks 038W]
#check
  (AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegularAt.iff_fieldExtension :
    ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
      [Algebra.EssFiniteType k k'] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) (x : X)
      (x' : FieldExtension.baseChange k k' f),
      FieldExtension.toSource k k' f x' = x →
        (Scheme.Hom.IsGeometricallyRegularAt f x ↔
          Scheme.Hom.IsGeometricallyRegularAt (FieldExtension.toBase k k' f) x'))

/- Lemma 33.12.4 (2): geometric regularity is invariant under a finitely generated field
extension. -/
@[stacks 038W]
#check
  (AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegular.iff_fieldExtension :
    ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
      [Algebra.EssFiniteType k k'] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)),
      Scheme.Hom.IsGeometricallyRegular f ↔
        Scheme.Hom.IsGeometricallyRegular (FieldExtension.toBase k k' f))
