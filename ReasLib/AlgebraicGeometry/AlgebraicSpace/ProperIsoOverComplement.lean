module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProperIsoOverOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement

/-!
# Proper morphisms of algebraic spaces that are isomorphisms over a closed complement

A morphism `f : X' ⟶ X` is proper and an isomorphism over the complementary
open of a closed immersion `i : Z ⟶ X` when it is proper and an isomorphism
over `closedImmersionComplementι i`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X' ⟶ X` of algebraic spaces is proper and an isomorphism
over the complementary open of a closed immersion `i : Z ⟶ X` when `f` is
proper and `openInverseImageTo f (closedImmersionComplementι i)` is an
isomorphism. -/
def IsProperIsoOverComplement {S : Scheme.{u}} {X' X Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] : Prop :=
  IsProperIsoOverOpen f (closedImmersionComplementι i)

/-- `IsProperIsoOverComplement f i` is properness of `f` together with
`IsIsoOverOpen f` of the complement immersion of `i`. -/
theorem isProperIsoOverComplement_iff {S : Scheme.{u}} {X' X Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    IsProperIsoOverComplement f i ↔
      Proper f ∧ IsIsoOverOpen f (closedImmersionComplementι i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
