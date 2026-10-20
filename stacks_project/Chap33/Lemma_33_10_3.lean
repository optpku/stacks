module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.Criteria
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry PerfectClosure

noncomputable section

universe u

variable {k : Type u} [Field k]

/- Lemma 33.10.3: for a scheme `X` over the field `k`, geometric normality is equivalent to
normality after every field extension, after every essentially finite type field extension,
after every finite purely inseparable field extension, on every affine-open section algebra, and
after base change to the perfect closure. -/
@[stacks 038O] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyNormal_tfae :
    ∀ X : Over (Spec (CommRingCat.of k)),
      List.TFAE [
        SchemeOverField.geometricallyNormal X,
        ∀ (k' : Type u) [Field k'] [Algebra k k'],
          Scheme.isNormal (FieldExtension.baseChange k k' X.hom),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
          Scheme.isNormal (FieldExtension.baseChange k k' X.hom),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'],
          Scheme.isNormal (FieldExtension.baseChange k k' X.hom),
        SchemeOverField.affineOpenSectionsGeometricallyNormal X,
        Scheme.isNormal (FieldExtension.baseChange k (kᵖᵉʳᶠ) X.hom)
      ])
