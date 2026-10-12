/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ProjectionFormula.Affine

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 36.5.3: for an affine morphism `f : X ⟶ S` and
`E : D_QCoh(𝒪_S)`, the object `Rf_* Lf^* E` is isomorphic to
`E ⊗ᴸ f_*𝒪_X`. -/
@[stacks 08I9] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affinePushforwardPullback_isomorphic :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsAffineHom f]
      (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent S),
      CategoryTheory.IsIsomorphic
        ((AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).obj
          ((AlgebraicGeometry.Scheme.DerivedQCoh.pullback f).obj E))
        (AlgebraicGeometry.Scheme.DerivedQCoh.tensorObj E
          (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardStructureSheaf f)))
