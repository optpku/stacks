/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Surjective
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite projective modules over a surjective ring pullback

The canonical base-change functor restricts to finite projective modules and is an equivalence
onto pullback triples whose two components are finite projective.

@stack 0D2J
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.Pullback.FiniteProjective

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

/-- The object property on pullback-module triples requiring both components to be finite
projective. -/
@[stacks 0D2J "componentwise finite-projective pullback modules"]
def property : ObjectProperty (Pullback.Category S.toA S.fromAprime) :=
  fun X => ModuleCat.finiteProjective B X.fst ∧ ModuleCat.finiteProjective A' X.snd

/-- The full subcategory of pullback-module triples with finite-projective components. -/
@[stacks 0D2J "finite-projective pullback module category"]
abbrev Category := (property S).FullSubcategory

/-- Base change from the pullback ring sends a finite-projective module to a pullback triple with
finite-projective components. -/
@[stacks 0D2J "finite projectivity after pullback base change"]
theorem baseChange_mem (L : ModuleCat.FiniteProjective S.Bprime) :
    property S
      ((ModuleCat.extendScalarsToPullback S.toA S.fromAprime
        S.bprimeToB S.bprimeToAprime S.comm).obj L.obj) := sorry

/-- The canonical base-change functor restricted to finite-projective modules. -/
@[stacks 0D2J "finite-projective pullback base-change functor"]
def baseChangeFunctor : ModuleCat.FiniteProjective S.Bprime ⥤ Category S :=
  (property S).lift
    ((ModuleCat.finiteProjective S.Bprime).ι ⋙
      ModuleCat.extendScalarsToPullback S.toA S.fromAprime
        S.bprimeToB S.bprimeToAprime S.comm)
    (baseChange_mem S)

/-- Base change is an equivalence between finite-projective modules over the pullback ring and
pullback triples with finite-projective components. -/
@[stacks 0D2J "equivalence on finite-projective pullback modules"]
theorem baseChangeFunctor_isEquivalence : Functor.IsEquivalence (baseChangeFunctor S) := sorry

end CategoryTheory.ModuleCat.Pullback.FiniteProjective
