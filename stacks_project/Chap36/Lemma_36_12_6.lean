/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Pushforward

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 36.12.6: for a finite morphism `f : X ⟶ Y` whose pushed-forward structure sheaf is
pseudo-coherent, `E` is `m`-pseudo-coherent if and only if its derived pushforward is
`m`-pseudo-coherent. -/
@[stacks 09VB] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.isMPseudoCoherent_iff_pushforward_of_isFinite :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsFinite f],
      SheafOfModules.IsPseudoCoherent
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj
            (SheafOfModules.unit X.ringCatSheaf : X.Modules)) →
        ∀ (E : DerivedCategory.CohomologyIn
          (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ),
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent E.obj m ↔
            AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
              ((AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).obj E).obj m)
