/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap83.Lemma_83_5_17_Comparison
public import stacks_project.Chap83.Definition_83_5_8_Invariant
public import stacks_project.Chap83.Definition_83_5_13_SetTheoretic
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Surjectivity criteria for set-theoretic invariance and orbit-separation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- Lemma 83.5.17 (1): a morphism `φ : U ⟶ X` over `B` is set-theoretically invariant
for a pre-relation `P` if and only if the projection `p = P.toRelation φ` is
surjective. -/
@[stacks 049Y]
theorem isSetTheoreticallyInvariant_iff_surjective
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.IsSetTheoreticallyInvariant φ ↔ Surjective (P.toRelation φ).left :=
  sorry

/-- Lemma 83.5.17 (2): if `P` is a set-theoretic pre-equivalence relation, then `φ`
separates orbits if and only if the projections `p = P.toRelation φ` and
`q = P.toKernelPair φ` are surjective. -/
@[stacks 049Y]
theorem separatesOrbits_iff_surjective
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (hP : P.IsSetTheoreticPreEquivalence) :
    P.SeparatesOrbits φ ↔
      Surjective (P.toRelation φ).left ∧ Surjective (P.toKernelPair φ).left :=
  sorry

/-- Lemma 83.5.17 (3): if the projections `p = P.toRelation φ` and
`q = P.toKernelPair φ` are surjective, then `P` is a set-theoretic pre-equivalence
relation and `φ` separates orbits. -/
@[stacks 049Y]
theorem isSetTheoreticPreEquivalence_of_surjective
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (hp : Surjective (P.toRelation φ).left)
    (hq : Surjective (P.toKernelPair φ).left) :
    P.IsSetTheoreticPreEquivalence ∧ P.SeparatesOrbits φ :=
  sorry

/-- Lemma 83.5.17 (4): if `φ` is `R`-invariant and `P` is a set-theoretic
pre-equivalence relation, then `φ` separates orbits if and only if the induced
morphism `P.induced hφ : P.left ⟶ pullback φ φ` is surjective. -/
@[stacks 049Y]
theorem separatesOrbits_iff_surjective_induced
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (hφ : P.IsInvariant φ)
    (hP : P.IsSetTheoreticPreEquivalence) :
    P.SeparatesOrbits φ ↔ Surjective (P.induced hφ).left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
