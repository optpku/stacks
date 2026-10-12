/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.Criteria
import StacksCheckRecall

@[expose] public section

open scoped PerfectClosure

universe u

/- Lemma 33.6.4: for a scheme over a field of positive characteristic, geometric reducedness is
equivalent to reducedness after all field extensions, all finite purely inseparable field
extensions, the canonical first Frobenius-root extension, the perfect closure, or an algebraic
closure, and to geometric reducedness of every affine-open section algebra. -/
@[stacks 035X] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReduced_tfae :
    ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      List.TFAE [
        AlgebraicGeometry.SchemeOverField.geometricallyReduced X,
        ∀ (k' : Type u) [Field k'] [Algebra k k'],
          AlgebraicGeometry.IsReduced
            (AlgebraicGeometry.FieldExtension.baseChange k k' X.hom),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'],
          AlgebraicGeometry.IsReduced
            (AlgebraicGeometry.FieldExtension.baseChange k k' X.hom),
        AlgebraicGeometry.IsReduced
          (AlgebraicGeometry.FieldExtension.baseChange k
            (IntermediateField.onePthRootExtension k p) X.hom),
        AlgebraicGeometry.IsReduced
          (AlgebraicGeometry.FieldExtension.baseChange k (kᵖᵉʳᶠ) X.hom),
        AlgebraicGeometry.IsReduced
          (AlgebraicGeometry.FieldExtension.baseChange k (AlgebraicClosure k) X.hom),
        ∀ U : X.left.affineOpens,
          Algebra.IsGeometricallyReduced k
            (AlgebraicGeometry.SchemeOverField.sectionsAlg X (U : X.left.Opens))
      ])
