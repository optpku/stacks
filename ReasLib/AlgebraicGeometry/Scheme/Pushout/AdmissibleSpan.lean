/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Pushout

/-- The admissibility conditions on a span of schemes over a fixed base used in
the scheme-pushout construction. -/
class IsAdmissibleSpan {S : Scheme.{u}} {Z X Y : Over S}
    (i : Z ⟶ X) (j : Z ⟶ Y) : Prop
    extends IsClosedImmersion i.left, IsIntegralHom j.left where
  /-- Every fibre of `j` maps under `i` into an affine open of `X`. -/
  exists_affineOpen (y : Y.left) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧
      ∀ z : Z.left, j.left z = y → i.left z ∈ U

namespace IsAdmissibleSpan

variable {S : Scheme.{u}} {Z X Y : Over S} {i : Z ⟶ X} {j : Z ⟶ Y}

/-- The span consisting of two identity morphisms is admissible. -/
instance instIdentity (X : Over S) : IsAdmissibleSpan (𝟙 X) (𝟙 X) := sorry

/-- The three conditions characterizing an admissible span. -/
theorem iff (i : Z ⟶ X) (j : Z ⟶ Y) :
    IsAdmissibleSpan i j ↔
      IsClosedImmersion i.left ∧ IsIntegralHom j.left ∧
        ∀ y : Y.left, ∃ U : X.left.Opens, IsAffineOpen U ∧
          ∀ z : Z.left, j.left z = y → i.left z ∈ U := sorry

/-- The fibre over a point is contained in the inverse image of a suitable affine open. -/
theorem fiber_subset_preimage [IsAdmissibleSpan i j] (y : Y.left) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧
      {z : Z.left | j.left z = y} ⊆ (i.left ⁻¹ᵁ U : Set Z.left) := sorry

/-- Every point in one target of an admissible span has an affine neighborhood whose
inverse image agrees with that of an affine open in the other target. -/
theorem exists_affineOpen_preimage_eq [IsAdmissibleSpan i j] (y : Y.left) :
    ∃ (U : X.left.Opens) (_ : IsAffineOpen U) (V : Y.left.Opens) (_ : IsAffineOpen V),
      i.left ⁻¹ᵁ U = j.left ⁻¹ᵁ V ∧ y ∈ V := sorry

end IsAdmissibleSpan

end AlgebraicGeometry.Scheme.Pushout
