/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.Proper

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField.Normalization

/-- Normalization preserves topological Krull dimension for schemes locally of finite type
over a field. -/
theorem topologicalKrullDim_eq
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    topologicalKrullDim (SchemeOverField.normalization X).left =
      topologicalKrullDim X.left := sorry

end AlgebraicGeometry.SchemeOverField.Normalization
