/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Lemma_106_4_1_Properties
import StacksCheckRecall

/- Lemma 106.4.1 (1): affine morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.affine_iff

/- Lemma 106.4.1 (2): surjective morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.surjective_iff

/- Lemma 106.4.1 (3): quasi-compact morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.quasiCompact_iff

/- Lemma 106.4.1 (4): universally closed morphisms are invariant under a morphism
of thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.universallyClosed_iff

/- Lemma 106.4.1 (5): integral morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.isIntegralHom_iff

/- Lemma 106.4.1 (6): universally injective morphisms are invariant under a
morphism of thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.universallyInjective_iff

/- Lemma 106.4.1 (7): universally open morphisms are invariant under a morphism
of thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.universallyOpen_iff

/- Lemma 106.4.1 (8): quasi-DM morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.quasiDM_iff

/- Lemma 106.4.1 (9): DM morphisms are invariant under a morphism of thickenings
of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.dm_iff

/- Lemma 106.4.1 (10): quasi-separated morphisms are invariant under a morphism
of thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.quasiSeparated_iff

/- Lemma 106.4.1 (10): separated morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.separated_iff

/- Lemma 106.4.1 (11): representable morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.relativelyRepresentable_iff

/- Lemma 106.4.1 (12): morphisms representable by algebraic spaces are invariant
under a morphism of thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.relativelyRepresentableByAlgebraicSpaces_iff
