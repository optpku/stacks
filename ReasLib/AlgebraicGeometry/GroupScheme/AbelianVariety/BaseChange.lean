module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.Over

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Field-extension base change preserves the property of being an abelian variety. -/
instance instAbelianVariety (A : SchemeOverField k) [GrpObj A] [AbelianVariety A] :
    AbelianVariety (baseChange k K A) := sorry

end AlgebraicGeometry.FieldExtension.Over
