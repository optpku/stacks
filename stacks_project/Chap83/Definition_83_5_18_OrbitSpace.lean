/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap83.Definition_83_4_1_Invariant
public import stacks_project.Chap83.Definition_83_5_8_Invariant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.OrbitSpace

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

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticallyInvariant_of_isInvariant :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X},
    P.IsInvariantHom φ → P.IsSetTheoreticallyInvariant φ)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsOrbitSpace :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B},
    PreRelation U → (U ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isOrbitSpace_iff :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X),
    IsOrbitSpace P φ ↔
      P.IsInvariantHom φ ∧ P.SeparatesOrbits φ ∧ Surjective φ.left)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsOrbitSpace.instIdDiag :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B),
    (ofHom (diag U : U ⟶ U ⨯ U)).IsOrbitSpace (𝟙 U))

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsOrbitSpace.surjective_left :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [h : P.IsOrbitSpace φ], Surjective φ.left)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsOrbitSpace.spec :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [P.IsOrbitSpace φ],
    P.IsInvariantHom φ ∧
      P.IsSetTheoreticallyInvariant φ ∧
        (∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
          x ≫ φ = y ≫ φ → P.orbitEquivalent kbar x y) ∧
        Surjective φ.left)

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
