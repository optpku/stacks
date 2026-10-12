/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap83.Definition_83_4_1_Invariant
public import stacks_project.Chap83.Definition_83_5_8_Invariant

/-!
# Orbit spaces of a pre-relation

A morphism of algebraic spaces over a base is an orbit space for a pre-relation when it
equalizes the two projections, separates geometric `R`-orbits, and is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

/-- An `R`-invariant morphism is set-theoretically `R`-invariant. -/
theorem isSetTheoreticallyInvariant_of_isInvariant {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (h : P.IsInvariant φ) :
    P.IsSetTheoreticallyInvariant φ :=
  sorry

/-- A morphism `φ : U ⟶ X` over `B` is an orbit space for a pre-relation `P` when it is
`R`-invariant, separates `R`-orbits, and is surjective. -/
@[mk_iff]
class IsOrbitSpace {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop where
  /-- The morphism equalizes the two projections of the pre-relation. -/
  invariant : P.IsInvariant φ
  /-- The morphism separates `R`-orbits on geometric points of `B`. -/
  separatesOrbits : P.SeparatesOrbits φ
  /-- The underlying morphism of algebraic spaces is surjective. -/
  surjective : Surjective φ.left

namespace IsOrbitSpace

/-- The identity of `U` is an orbit space for the diagonal pre-relation. -/
instance instIdDiag {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    (ofHom (diag U : U ⟶ U ⨯ U)).IsOrbitSpace (𝟙 U) :=
  sorry

/-- An orbit space is surjective on underlying algebraic spaces. -/
theorem surjective_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [h : P.IsOrbitSpace φ] : Surjective φ.left :=
  h.surjective

/-- An orbit space is `R`-invariant, set-theoretically `R`-invariant, separates geometric
`R`-orbits, and is surjective. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [P.IsOrbitSpace φ] :
    P.IsInvariant φ ∧
      P.IsSetTheoreticallyInvariant φ ∧
        (∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
          x ≫ φ = y ≫ φ → P.orbitEquivalent kbar x y) ∧
        Surjective φ.left :=
  sorry

end IsOrbitSpace

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
