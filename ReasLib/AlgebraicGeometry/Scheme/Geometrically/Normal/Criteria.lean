module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure
public import ReasLib.RingTheory.Normal.GeometricallyNormal.FieldTests

/-!
# Criteria for geometrically normal schemes over a field

This leaf gives field-extension, affine-open, and perfect-closure criteria for
geometric normality of a scheme over a field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry PerfectClosure

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- For a scheme over a field, geometric normality is equivalent to normality after every field
extension, after every essentially finite type field extension, after every finite purely
inseparable field extension, on every affine-open section algebra, and after base change to the
perfect closure. -/
@[stacks 038O]
theorem geometricallyNormal_tfae (X : Over (Spec (CommRingCat.of k))) :
    List.TFAE [
      geometricallyNormal X,
      ∀ (k' : Type u) [Field k'] [Algebra k k'],
        Scheme.isNormal (FieldExtension.baseChange k k' X.hom),
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
        Scheme.isNormal (FieldExtension.baseChange k k' X.hom),
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        Scheme.isNormal (FieldExtension.baseChange k k' X.hom),
      affineOpenSectionsGeometricallyNormal X,
      Scheme.isNormal (FieldExtension.baseChange k (kᵖᵉʳᶠ) X.hom)
    ] := sorry

end AlgebraicGeometry.SchemeOverField
