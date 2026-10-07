module

public import Mathlib.FieldTheory.SeparableClosure

@[expose] public section

/-!
# Degrees of field extensions

Scoped notation for the cardinal, separable, and inseparable degrees of a field extension. The
underlying owners remain `Module.rank`, `Field.sepDegree`, and `Field.insepDegree`.
-/

namespace FieldExtensionDegree
end FieldExtensionDegree

/-- Cardinal degree of a field extension. -/
scoped[FieldExtensionDegree] notation:max "[" E " : " F "]" => Module.rank F E

/-- Separable degree of a field extension. -/
scoped[FieldExtensionDegree] notation:max "[" E " : " F "]ₛ" => Field.sepDegree F E

/-- Inseparable degree of a field extension. -/
scoped[FieldExtensionDegree] notation:max "[" E " : " F "]ᵢ" => Field.insepDegree F E
