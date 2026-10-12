/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Surjective
public import ReasLib.Algebra.Category.ModuleCat.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat modules over a surjective ring pullback

This file restricts the fibre-product module adjunction to the full subcategories of flat
modules.  The functors are explicit lifts of the shared base-change and right-adjoint owners;
only preservation, invertibility, and equivalence propositions remain proof obligations.

@stack 0D2I
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

namespace CategoryTheory.ModuleCat.Pullback.Flat

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

/-- The pullback-module property requiring flatness of both component modules. -/
@[stacks 0D2I "componentwise flat pullback modules"]
def property : ObjectProperty (Pullback.Category S.toA S.fromAprime) :=
  fun X ↦ Module.Flat B X.fst ∧ Module.Flat A' X.snd

/-- The full subcategory of pullback-module triples with flat components. -/
@[stacks 0D2I "componentwise flat pullback module category"]
abbrev Category := (property S).FullSubcategory

/-- Base change from the pullback ring sends a flat module to a pullback triple with flat
components. -/
@[stacks 0D2I "flatness after pullback base change"]
theorem baseChange_mem (L : ModuleCat.Flat S.Bprime) :
    property S ((ModuleCat.extendScalarsToPullback S.toA S.fromAprime
      S.bprimeToB S.bprimeToAprime S.comm).obj L.obj) := sorry

/-- The canonical base-change functor restricted to flat modules. -/
@[stacks 0D2I "flat pullback base-change functor"]
def baseChangeFunctor : ModuleCat.Flat S.Bprime ⥤ Category S :=
  (property S).lift
    ((ModuleCat.flat S.Bprime).ι ⋙
      ModuleCat.extendScalarsToPullback S.toA S.fromAprime
        S.bprimeToB S.bprimeToAprime S.comm)
    (baseChange_mem S)

/-- Lemma 15.6.8 (1): the fibre-product module of a pullback triple with flat components is flat
over the pullback ring. -/
@[stacks 0D2I "(1), flat fibre-product module"]
theorem rightAdjoint_mem (X : Category S) :
    Module.Flat S.Bprime
      ((Pullback.rightAdjoint S.bprimeToB S.bprimeToAprime S.comm).obj X.obj) := sorry

/-- The fibre-product module functor restricted to the flat full subcategories. -/
@[stacks 0D2I "flat fibre-product module functor"]
def rightAdjointFunctor : Category S ⥤ ModuleCat.Flat S.Bprime :=
  (ModuleCat.flat S.Bprime).lift
    ((property S).ι ⋙ Pullback.rightAdjoint S.bprimeToB S.bprimeToAprime S.comm)
    (rightAdjoint_mem S)

/-- Lemma 15.6.8 (2): the adjunction unit is an isomorphism on every flat module over the
pullback ring. -/
@[stacks 0D2I "(2), flat module reconstruction"]
theorem unit_isIso (L : ModuleCat S.Bprime) (hL : Module.Flat S.Bprime L) :
    IsIso ((Pullback.adjunction S.bprimeToB S.bprimeToAprime S.comm).unit.app L) := sorry

/-- Lemma 15.6.8 (3): base change is an equivalence from flat modules over the pullback ring to
pullback triples with flat components. -/
@[stacks 0D2I "(3), equivalence on flat modules"]
theorem baseChangeFunctor_isEquivalence : Functor.IsEquivalence (baseChangeFunctor S) := sorry

end CategoryTheory.ModuleCat.Pullback.Flat
