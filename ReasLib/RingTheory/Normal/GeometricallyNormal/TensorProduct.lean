module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.GeometricallyNormal.FieldTests
public import ReasLib.RingTheory.Normal.Ring

/-!
# Normality of tensor products with a geometrically normal factor

This leaf owns the reusable tensor-product consequence of geometric normality.
The factor roles are explicit in the theorem names: the left factor is the
geometrically normal algebra in the tagged source theorem, while the right
factor is the normal algebra. The symmetric bridge carries the same source
tag and mathematical content with the roles exchanged.

The result is an explicit theorem rather than a global `IsNormalRing` instance.
Normality of a tensor product is a derived fact and registering both tensor
orientations globally would make typeclass search ambiguous and needlessly
couple unrelated tensor-product constructions.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

variable {k : Type u} {A : Type v} {B : Type w}
variable [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/- The source theorem is oriented with the geometric hypothesis on `A`. -/
/-- Lemma 10.165.5 (Stacks tag `06DF`): tensoring a geometrically normal
`k`-algebra on the left with a normal `k`-algebra on the right gives a normal
ring. -/
@[stacks 06DF]
theorem isNormalRing_of_isGeometricallyNormal_left
    [Algebra.IsGeometricallyNormal k A] [IsNormalRing B] :
    IsNormalRing (A ⊗[k] B) := sorry

/-- Normality of the tensor product with the geometric factor on the right.
This is the symmetric bridge to `isNormalRing_of_isGeometricallyNormal_left`.
-/
@[stacks 06DF "symmetric factor order"]
theorem isNormalRing_of_isGeometricallyNormal_right
    [IsNormalRing A] [Algebra.IsGeometricallyNormal k B] :
    IsNormalRing (A ⊗[k] B) := sorry

end Algebra.TensorProduct
