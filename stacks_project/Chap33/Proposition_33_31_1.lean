/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.IntegralClosure.Uniqueness

open AlgebraicGeometry CategoryTheory

universe u

/- Proposition 33.31.1: for two locally finite type structure morphisms from the same connected
reduced scheme to spectra of fields, the integral closures of the two base fields in the common
global-sections ring are equal. -/
@[stacks 04MK] #check
  (AlgebraicGeometry.Scheme.Hom.baseFieldIntegralClosure_eq_of_connectedReduced_of_locallyOfFiniteType :
    ∀ {X : Scheme.{u}} {k₁ k₂ : Type u} [Field k₁] [Field k₂]
      (a : X ⟶ Spec (CommRingCat.of k₁)) (b : X ⟶ Spec (CommRingCat.of k₂))
      [LocallyOfFiniteType a] [LocallyOfFiniteType b] [ConnectedSpace X] [IsReduced X],
      a.baseFieldIntegralClosure = b.baseFieldIntegralClosure)
