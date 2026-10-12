/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap83.Definition_83_8_1_InvariantFunctions
public import stacks_project.Chap83.Definition_83_9_1_Invariant

/-!
# Good quotients of a pre-relation

A morphism of algebraic spaces over a base is a good quotient of a pre-relation when it is
invariant, affine, and surjective, condition (3) holds universally, and the functions on the
target are the invariant functions on the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- A morphism `φ : U ⟶ X` of algebraic spaces over `B` is a good quotient of a pre-relation
`P` when it is `R`-invariant, affine, and surjective, condition (3) holds universally, and the
functions on `X` are the `R`-invariant functions on `U`. -/
class IsGoodQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop where
  /-- The morphism equalizes the two projections of the pre-relation. -/
  invariant : P.IsInvariantHom φ
  /-- The underlying morphism of algebraic spaces is affine. -/
  affine : Affine φ.left
  /-- The underlying morphism of algebraic spaces is surjective. -/
  surjective : Surjective φ.left
  /-- Condition (3) holds after every base change of the invariant morphism in `Over B`. -/
  universallyIntersectInvariantClosed :
    UniversallyIntersectInvariantClosed P φ invariant
  /-- The natural map `𝒪_X ⟶ (φ_* 𝒪_U)^R` is an isomorphism. -/
  functionsAreInvariant : P.HasInvariantFunctions φ invariant

/-- A good quotient is an affine morphism of algebraic spaces. -/
theorem toAffine {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} [h : IsGoodQuotient P φ] : Affine φ.left :=
  sorry

/-- A good quotient is a surjective morphism of algebraic spaces. -/
theorem toSurjective {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} [h : IsGoodQuotient P φ] : Surjective φ.left :=
  sorry

/-- A good quotient is an `R`-invariant morphism. -/
theorem toIsInvariantHom {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} [h : IsGoodQuotient P φ] : P.IsInvariantHom φ :=
  sorry

/-- A good quotient induces an isomorphism `𝒪_X ≃ (φ_* 𝒪_U)^R`. -/
instance instIsIso_structureSheafToInvariantFunctions {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} {P : PreRelation U} {φ : U ⟶ X} [h : IsGoodQuotient P φ] :
    IsIso (P.structureSheafToInvariantFunctions φ h.invariant) :=
  h.functionsAreInvariant

/-- Being a good quotient is equivalent to the five source clauses. -/
theorem isGoodQuotient_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    IsGoodQuotient P φ ↔
      ∃ hφ : P.IsInvariantHom φ,
        Affine φ.left ∧ Surjective φ.left ∧
          UniversallyIntersectInvariantClosed P φ hφ ∧ P.HasInvariantFunctions φ hφ :=
  sorry

/-- A good quotient is invariant, affine, and surjective, satisfies universal condition (3),
and has functions equal to the invariant functions. -/
theorem isGoodQuotient_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} [h : IsGoodQuotient P φ] :
    P.IsInvariantHom φ ∧ Affine φ.left ∧ Surjective φ.left ∧
      UniversallyIntersectInvariantClosed P φ h.invariant ∧
        P.HasInvariantFunctions φ h.invariant :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
