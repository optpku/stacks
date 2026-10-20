module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Refined valuative criterion for universal closedness

A quasi-compact morphism of algebraic spaces that satisfies uniqueness and
existence of the valuative criterion along a quasi-compact dominant morphism is
universally closed, and is separated if it is moreover quasi-separated.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.Along

/-- Let `S` be a scheme, and let `f : X ⟶ Y` and `h : U ⟶ X`
be quasi-compact morphisms of algebraic spaces over `S`. If `|h|(|U|)` is dense
in `|X|`, every valuative solid square whose generic arrow factors through `h`
has at most one dotted lift `Spec(A) ⟶ X`, and every such square admits a
dominating valuation-ring extension with a morphism `Spec(A') ⟶ X` filling the
extended diagram, then `f` is universally closed. -/
@[stacks 089G]
theorem universallyClosed {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (h : U ⟶ X) [QuasiCompact f] [QuasiCompact h] [Dominant h]
    (h_uniqueness : Uniqueness h f) (h_existence : Existence h f) :
    UniversallyClosed f :=
  sorry

/-- A quasi-separated quasi-compact morphism of algebraic spaces is separated
if restricted valuative uniqueness and existence after dominating valuation-ring
extensions hold along a quasi-compact morphism with dense image. -/
@[stacks 089G]
theorem separated {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (h : U ⟶ X) [QuasiCompact f] [QuasiCompact h] [Dominant h] [QuasiSeparated f]
    (h_uniqueness : Uniqueness h f) (h_existence : Existence h f) :
    Separated f :=
  sorry

end ValuativeCriterion.Along

end AlgebraicGeometry.AlgebraicSpace
