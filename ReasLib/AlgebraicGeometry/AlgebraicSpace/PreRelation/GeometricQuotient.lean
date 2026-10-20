module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Submersive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.OrbitSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.InvariantFunctions

/-!
# Geometric quotients of a pre-relation

A morphism of algebraic spaces over a base is a geometric quotient of a pre-relation when it is
an orbit space, is universally submersive, and identifies functions on the quotient with
`R`-invariant functions on the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

/-- A morphism `φ : U ⟶ X` over `B` is a geometric quotient of a pre-relation `P` when it is an
orbit space, is universally submersive, and the functions on `X` are the `R`-invariant functions
on `U`. -/
@[mk_iff]
class IsGeometricQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop extends IsOrbitSpace P φ where
  /-- The underlying morphism of algebraic spaces is universally submersive. -/
  universallySubmersive : UniversallySubmersive φ.left
  /-- The functions on `X` are the `R`-invariant functions on `U`. -/
  functionsAreInvariant : P.HasInvariantFunctions φ invariant

namespace IsGeometricQuotient

/-- The identity of `U` is a geometric quotient for the diagonal pre-relation. -/
instance instIdDiag {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    (ofHom (Limits.diag U : U ⟶ U ⨯ U)).IsGeometricQuotient (𝟙 U) :=
  sorry

/-- A geometric quotient is universally submersive on underlying algebraic spaces. -/
theorem universallySubmersive_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [P.IsGeometricQuotient φ] :
    UniversallySubmersive φ.left :=
  sorry

/-- A geometric quotient induces an isomorphism `𝒪_X ≃ (φ_* 𝒪_U)^R`. -/
instance instIsIso_structureSheafToInvariantFunctions {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} {P : PreRelation U} {φ : U ⟶ X} [h : P.IsGeometricQuotient φ] :
    IsIso (P.structureSheafToInvariantFunctions φ h.invariant) :=
  h.functionsAreInvariant

/-- A geometric quotient is an orbit space, is universally submersive, and identifies functions
on `X` with `R`-invariant functions on `U`. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [h : P.IsGeometricQuotient φ] :
    P.IsOrbitSpace φ ∧ UniversallySubmersive φ.left ∧ P.HasInvariantFunctions φ h.invariant :=
  sorry

end IsGeometricQuotient

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
