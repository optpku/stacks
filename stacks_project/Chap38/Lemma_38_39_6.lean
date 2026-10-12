/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.FlatProperDescent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 38.39.6: A finite locally free module on the source of a flat proper
morphism to a normal Noetherian scheme, free after every height-one stalk base
change, is the pullback of a finite locally free module on the base. -/
@[stacks 0EXG] #check
  (AlgebraicGeometry.Scheme.Hom.FlatDescent.existsFiniteLocallyFreePullback :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f] [IsNoetherian S]
      (hSnormal : S.isNormal)
      [IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)]
      (E : X.Modules) [E.IsFiniteLocallyFree]
      (hfree : ∀ s : S, ringKrullDim (S.presheaf.stalk s) = 1 →
        ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk s))).obj E).IsFree),
      ∃ (F : S.Modules) (_ : F.IsFiniteLocallyFree),
        Nonempty (E ≅ (Scheme.Modules.pullback f).obj F))
