module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Normalization.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal

/-!
# Geometric normality after normalization and field extension

This leaf records geometric normality of normalized base changes after suitable finite purely
inseparable extensions of the base field.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

namespace geometricallyNormal

/-- An algebraic scheme over a field has a finite purely inseparable extension over which its
normalized base change is geometrically normal. -/
@[stacks 0BXT]
theorem exists_finitePurelyInseparableExtension_normalization
    (X : SchemeOverField k) [Algebraic X] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
      geometricallyNormal (FieldExtension.Normalization.baseChange X k') := sorry

end geometricallyNormal

end AlgebraicGeometry.SchemeOverField
