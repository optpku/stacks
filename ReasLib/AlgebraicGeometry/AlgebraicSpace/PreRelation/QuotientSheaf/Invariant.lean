/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Descent

/-!
# Invariant morphisms and quotient sheaves

An invariant morphism from a pre-relation factors canonically through its quotient sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- An invariant morphism equalizes the universe-raised source and target maps. -/
theorem isInvariant_toSheaf_map {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) :
    toSheaf.map P.t.left ≫ toSheaf.map φ.left =
      toSheaf.map P.s.left ≫ toSheaf.map φ.left :=
  sorry

/-- The universe-raised quotient presheaf of an invariant morphism, as a map to `X`. -/
def quotientPresheafFactor {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) :
    P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u} ⟶ (toSheaf.obj X.left).obj :=
  P.quotientPresheafLift (toSheaf.map φ.left) (P.isInvariant_toSheaf_map hφ)

/-- The component of `quotientPresheafFactor` is the equalizing lift of `toSheaf.map φ.left`. -/
theorem quotientPresheafFactor_app {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (T : (Over S)ᵒᵖ) :
    (P.quotientPresheafFactor hφ).app T =
      P.quotientSheafLiftApp (toSheaf.map φ.left) (P.isInvariant_toSheaf_map hφ) T :=
  sorry

/-- The canonical sheaf morphism `U/R ⟶ X` induced by an invariant morphism `φ`. -/
def quotientSheafFactor {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) :
    P.quotientSheaf ⟶ toSheaf.obj X.left :=
  P.quotientSheafLift (toSheaf.map φ.left) (P.isInvariant_toSheaf_map hφ)

/-- The structure map of `U/R` over `X` recovers `φ` after composing with the quotient map. -/
theorem quotientSheafFactor_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) :
    P.quotientMap ≫ P.quotientSheafFactor hφ = toSheaf.map φ.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
