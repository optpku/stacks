module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

@[expose] public section

open AlgebraicGeometry CommRingCat CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (of k))

/-- Quasi-affineness descends along an arbitrary extension of the ground field. -/
theorem isQuasiAffine_of_isQuasiAffine_baseChangeToFieldExtension
    (hXK : (FieldExtension.baseChange k K f).IsQuasiAffine) :
    X.IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme.Hom
