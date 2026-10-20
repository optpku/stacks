module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Regular.Criteria
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.12.3: for a locally Noetherian scheme over a field, geometric regularity is
equivalent to regularity after every essentially finite type field extension, regularity after
every finite purely inseparable field extension, geometric regularity of every affine-open
section algebra, and that section-algebra condition on one affine open cover. -/
@[stacks 038V] #check
  (AlgebraicGeometry.SchemeOverField.isGeometricallyRegular_tfae :
    ∀ {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))
      [IsLocallyNoetherian X.left],
      List.TFAE [
        AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegular X.hom,
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
          AlgebraicGeometry.Scheme.Regular
            (AlgebraicGeometry.FieldExtension.baseChange k k' X.hom),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'],
          AlgebraicGeometry.Scheme.Regular
            (AlgebraicGeometry.FieldExtension.baseChange k k' X.hom),
        ∀ U : X.left.affineOpens,
          Algebra.IsGeometricallyRegular k
            (AlgebraicGeometry.SchemeOverField.sectionsAlg X (U : X.left.Opens)),
        ∃ 𝒰 : AlgebraicGeometry.Scheme.AffineOpenCover.{u, u} X.left,
          ∀ i : 𝒰.I₀,
            Algebra.IsGeometricallyRegular k
              (AlgebraicGeometry.SchemeOverField.sectionsAlg X (𝒰.f i).opensRange)
      ])
