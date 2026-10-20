/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.OrbitSeparation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoreticInvariant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

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

/-- A morphism `φ : U ⟶ X` over `B` is an orbit space for a pre-relation `P` when it is
invariant, separates geometric `R`-orbits, and is surjective. -/
@[mk_iff]
class IsOrbitSpace {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop where
  /-- The morphism equalizes the two projections of the pre-relation. -/
  invariant : P.IsInvariantHom φ
  /-- The morphism separates `R`-orbits on geometric points of `B`. -/
  separatesOrbits : P.SeparatesOrbits φ
  /-- The underlying morphism of algebraic spaces is surjective. -/
  surjective : Surjective φ.left

namespace IsOrbitSpace

/-- The identity of `U` is an orbit space for the diagonal pre-relation. -/
instance instIdDiag {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    (ofHom (CategoryTheory.Limits.diag U : U ⟶ U ⨯ U)).IsOrbitSpace (𝟙 U) :=
  sorry

/-- An orbit space is surjective on underlying algebraic spaces. -/
theorem surjective_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [h : P.IsOrbitSpace φ] : Surjective φ.left :=
  h.surjective

/-- An orbit space is invariant, set-theoretically invariant, separates geometric `R`-orbits,
and is surjective. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) [P.IsOrbitSpace φ] :
    P.IsInvariantHom φ ∧
      P.IsSetTheoreticallyInvariant φ ∧
        (∀ (kbar : GeometricPoint B) (x y : Over.mk kbar.hom ⟶ U),
          x ≫ φ = y ≫ φ → P.orbitEquivalent kbar x y) ∧
        Surjective φ.left :=
  sorry

end IsOrbitSpace

/-- For a set-theoretic pre-equivalence relation, a morphism is an orbit space if and only
if it is invariant, its induced morphism to the kernel pair is surjective, and it is
surjective. -/
theorem isOrbitSpace_iff_of_isSetTheoreticPreEquivalence
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (hP : P.IsSetTheoreticPreEquivalence) :
    P.IsOrbitSpace φ ↔
      P.IsInvariantHom φ ∧ (∀ hφ : P.IsInvariantHom φ, Surjective (P.induced hφ).left) ∧
        Surjective φ.left :=
  sorry

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
