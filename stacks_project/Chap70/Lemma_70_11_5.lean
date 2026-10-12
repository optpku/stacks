/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_11_5_Factorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.11.5: a locally of finite type quasi-affine morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S`, with `Y` quasi-compact and quasi-separated,
factors as a closed immersion `X ⟶ X'` over `Y` followed by a morphism
`X' ⟶ Y` of finite presentation. -/
@[stacks 0871] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_closedImmersion_factorization_of_locallyOfFiniteType_quasiAffine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.LocallyOfFiniteType f] [AlgebraicSpace.QuasiAffine f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
      (MorphismProperty.comp
        (@AlgebraicSpace.IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
        (@AlgebraicSpace.FinitePresentation S : MorphismProperty (AlgebraicSpace S))) f)
