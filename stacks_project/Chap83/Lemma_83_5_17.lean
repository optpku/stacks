module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.OrbitSeparation
import StacksCheckRecall

/-!
# Surjectivity criteria for set-theoretic invariance and orbit-separation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

/- Lemma 83.5.17 (1): set-theoretic invariance is equivalent to surjectivity of the projection to the relation. -/
@[stacks 049Y] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticallyInvariant_iff_surjective :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X),
      P.IsSetTheoreticallyInvariant φ ↔ Surjective (P.toRelation φ).left)

/- Lemma 83.5.17 (2): for a set-theoretic pre-equivalence relation, orbit separation is equivalent to surjectivity of both projections. -/
@[stacks 049Y] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.separatesOrbits_iff_surjective :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (hP : P.IsSetTheoreticPreEquivalence),
      P.SeparatesOrbits φ ↔
      Surjective (P.toRelation φ).left ∧ Surjective (P.toKernelPair φ).left)

/- Lemma 83.5.17 (3): surjectivity of both projections implies set-theoretic pre-equivalence and orbit separation. -/
@[stacks 049Y] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticPreEquivalence_of_surjective :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (hp : Surjective (P.toRelation φ).left)
    (hq : Surjective (P.toKernelPair φ).left),
      P.IsSetTheoreticPreEquivalence ∧ P.SeparatesOrbits φ)

/- Lemma 83.5.17 (4): for an invariant morphism and a set-theoretic pre-equivalence relation, orbit separation is equivalent to surjectivity of the induced morphism. -/
@[stacks 049Y] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.separatesOrbits_iff_surjective_induced :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (hφ : P.IsInvariantHom φ)
    (hP : P.IsSetTheoreticPreEquivalence),
      P.SeparatesOrbits φ ↔ Surjective (P.induced hφ).left)
