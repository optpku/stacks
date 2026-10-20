module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoretic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoreticInvariant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Surjectivity criteria for set-theoretic invariance and orbit-separation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- A morphism `φ : U ⟶ X` over `B` is set-theoretically invariant
for a pre-relation `P` if and only if the projection `p = P.toRelation φ` is
surjective. -/
theorem isSetTheoreticallyInvariant_iff_surjective
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.IsSetTheoreticallyInvariant φ ↔ Surjective (P.toRelation φ).left :=
  sorry

/-- If `P` is a set-theoretic pre-equivalence relation, then `φ`
separates orbits if and only if the projections `p = P.toRelation φ` and
`q = P.toKernelPair φ` are surjective. -/
theorem separatesOrbits_iff_surjective
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (hP : P.IsSetTheoreticPreEquivalence) :
    P.SeparatesOrbits φ ↔
      Surjective (P.toRelation φ).left ∧ Surjective (P.toKernelPair φ).left :=
  sorry

/-- If the projections `p = P.toRelation φ` and
`q = P.toKernelPair φ` are surjective, then `P` is a set-theoretic pre-equivalence
relation and `φ` separates orbits. -/
theorem isSetTheoreticPreEquivalence_of_surjective
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (hp : Surjective (P.toRelation φ).left)
    (hq : Surjective (P.toKernelPair φ).left) :
    P.IsSetTheoreticPreEquivalence ∧ P.SeparatesOrbits φ :=
  sorry

/-- If `φ` is `R`-invariant and `P` is a set-theoretic
pre-equivalence relation, then `φ` separates orbits if and only if the induced
morphism `P.induced hφ : P.left ⟶ pullback φ φ` is surjective. -/
theorem separatesOrbits_iff_surjective_induced
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (hφ : P.IsInvariantHom φ)
    (hP : P.IsSetTheoreticPreEquivalence) :
    P.SeparatesOrbits φ ↔ Surjective (P.induced hφ).left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
