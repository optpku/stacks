/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.59.9: for a finite morphism of schemes locally of finite type over a base,
an object of `D_QCoh(𝒪_X)` is relatively `m`-pseudo-coherent if and only if its derived
pushforward is relatively `m`-pseudo-coherent. -/
@[stacks 09UK] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.iff_pushforward_of_isFinite :
    ∀ {X Y S : Scheme.{u}} (π : X ⟶ Y) (g : Y ⟶ S) [IsFinite π]
      [LocallyOfFiniteType g] (E : Scheme.DerivedQCoh X) (m : ℤ),
    AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver (π ≫ g) E.obj m ↔
      AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver g
        ((Scheme.DerivedQCoh.pushforwardCohomologyIn π).obj E).obj m)
