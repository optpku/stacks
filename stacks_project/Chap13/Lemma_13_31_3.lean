/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.KInjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.31.3

The generic triangulated closure is owned by right orthogonals. Its
K-injective specialization is a reusable homotopy-category bridge.
-/

/- Lemma 13.31.3 (Stacks 090X) (1): K-injectivity of the first two vertices
of a distinguished homotopy triangle implies K-injectivity of the third. -/
@[stacks 090X] #check
  @CochainComplex.IsKInjective.of_distinguishedTriangle_obj₁_obj₂

/- Lemma 13.31.3 (Stacks 090X) (2): K-injectivity of the first and third
vertices of a distinguished homotopy triangle implies K-injectivity of the second. -/
@[stacks 090X] #check
  @CochainComplex.IsKInjective.of_distinguishedTriangle_obj₁_obj₃

/- Lemma 13.31.3 (Stacks 090X) (3): K-injectivity of the second and third
vertices of a distinguished homotopy triangle implies K-injectivity of the first. -/
@[stacks 090X] #check
  @CochainComplex.IsKInjective.of_distinguishedTriangle_obj₂_obj₃
