module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.PointwiseRegular
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Criteria for geometrically regular schemes over a field

This leaf gives field-extension and affine-local criteria for geometric regularity of a
locally Noetherian scheme over a field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- For a locally Noetherian scheme over a field, geometric regularity is equivalent to
regularity after every essentially finite type field extension, regularity after every finite
purely inseparable field extension, geometric regularity of every affine-open section algebra,
and that section-algebra condition on one affine open cover. -/
@[stacks 038V]
theorem isGeometricallyRegular_tfae
    (X : Over (Spec (CommRingCat.of k))) [IsLocallyNoetherian X.left] :
    List.TFAE [
      Scheme.Hom.IsGeometricallyRegular X.hom,
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
        Scheme.Regular (FieldExtension.baseChange k k' X.hom),
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        Scheme.Regular (FieldExtension.baseChange k k' X.hom),
      ∀ U : X.left.affineOpens,
        Algebra.IsGeometricallyRegular k (sectionsAlg X (U : X.left.Opens)),
      ∃ 𝒰 : Scheme.AffineOpenCover.{u, u} X.left,
        ∀ i : 𝒰.I₀,
          Algebra.IsGeometricallyRegular k (sectionsAlg X (𝒰.f i).opensRange)
    ] := sorry

end AlgebraicGeometry.SchemeOverField
