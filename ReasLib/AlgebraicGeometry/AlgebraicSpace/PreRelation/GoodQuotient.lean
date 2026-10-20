module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Topological
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.InvariantFunctions

/-!
# Good quotients of a pre-relation

A good quotient is invariant, affine, and surjective. After every target base change,
it maps invariant closed subsets to closed subsets and preserves their binary
intersections. Its target structure sheaf is canonically the sheaf of invariant functions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- A morphism `φ : U ⟶ X` over `B` is a good quotient of a pre-relation `P` if it is
invariant, affine, and surjective, maps invariant closed subsets to closed subsets and
preserves their binary intersections after every target base change, and the canonical
map from the target structure sheaf to the sheaf of invariant functions is an isomorphism. -/
class IsGoodQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop where
  /-- The morphism equalizes the two projections of the pre-relation. -/
  invariant : P.IsInvariantHom φ
  /-- The underlying morphism of algebraic spaces is affine. -/
  affine : Affine φ.left
  /-- The underlying morphism of algebraic spaces is surjective. -/
  surjective : Surjective φ.left
  /-- After every target base change in `Over B`, invariant closed subsets have closed
  images and their binary intersections are preserved. -/
  universallyIntersectInvariantClosed :
    UniversallyIntersectInvariantClosed P φ invariant
  /-- The natural map `𝒪_X ⟶ (φ_* 𝒪_U)^R` is an isomorphism. -/
  functionsAreInvariant : P.HasInvariantFunctions φ invariant

/-- A good quotient is an affine morphism of algebraic spaces. -/
theorem toAffine {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [h : IsGoodQuotient P φ] : Affine φ.left :=
  sorry

/-- A good quotient is a surjective morphism of algebraic spaces. -/
theorem toSurjective {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [h : IsGoodQuotient P φ] : Surjective φ.left :=
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

/-- Being a good quotient is equivalent to invariance, affineness, surjectivity,
universal closedness of invariant closed images and preservation of their binary
intersections, and the canonical identification of functions with invariant functions. -/
theorem isGoodQuotient_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    IsGoodQuotient P φ ↔
      ∃ hφ : P.IsInvariantHom φ,
        Affine φ.left ∧ Surjective φ.left ∧
          UniversallyIntersectInvariantClosed P φ hφ ∧ P.HasInvariantFunctions φ hφ :=
  sorry

/-- A good quotient is invariant, affine, and surjective, has closed invariant images
and preserves their binary intersections after every target base change, and identifies
the target structure sheaf with the sheaf of invariant functions. -/
theorem isGoodQuotient_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} [h : IsGoodQuotient P φ] :
    P.IsInvariantHom φ ∧ Affine φ.left ∧ Surjective φ.left ∧
      UniversallyIntersectInvariantClosed P φ h.invariant ∧
        P.HasInvariantFunctions φ h.invariant :=
  sorry

/-- The identity of `U` is a good quotient for the diagonal pre-relation. -/
instance IsGoodQuotient.instIdDiag {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    IsGoodQuotient (ofHom (Limits.diag U : U ⟶ U ⨯ U)) (𝟙 U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
