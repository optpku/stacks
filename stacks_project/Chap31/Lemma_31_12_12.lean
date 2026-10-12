/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.OpenComplement
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped ENat

universe u

/- Lemma 31.12.12: let `X` be an integral locally Noetherian scheme and let `U` be an open
subscheme whose complementary points have local-ring depth at least two. Then canonical pullback
and pushforward give an equivalence between coherent reflexive modules on `X` and on `U`. -/
@[stacks 0EBJ] #check (
  AlgebraicGeometry.Scheme.Modules.reflexiveCohOpenEquivalence :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (U : X.Opens)
      (hdepth : ∀ z : X, z ∉ U →
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)),
      AlgebraicGeometry.Scheme.Modules.ReflexiveCoh X ≌
        AlgebraicGeometry.Scheme.Modules.ReflexiveCoh (U : Scheme))

#check (
  AlgebraicGeometry.Scheme.Modules.reflexiveCohOpenEquivalence_functor :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (U : X.Opens)
      (hdepth : ∀ z : X, z ∉ U →
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)),
      (AlgebraicGeometry.Scheme.Modules.reflexiveCohOpenEquivalence U hdepth).functor =
        AlgebraicGeometry.Scheme.Modules.reflexiveCohOpenPullback U hdepth)

#check (
  AlgebraicGeometry.Scheme.Modules.reflexiveCohOpenEquivalence_inverse :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (U : X.Opens)
      (hdepth : ∀ z : X, z ∉ U →
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk z) (X.presheaf.stalk z)),
      (AlgebraicGeometry.Scheme.Modules.reflexiveCohOpenEquivalence U hdepth).inverse =
        AlgebraicGeometry.Scheme.Modules.reflexiveCohOpenPushforward U hdepth)
