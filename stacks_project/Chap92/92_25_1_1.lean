/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Ringed
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.DerivedPullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- 92.25.1.1 (1): the morphism of ringed topoi
i : (Sh(C_{X/Λ}), underline{O}_X) ⟶ (Sh(C_{X/Λ}), O)
is the identity on underlying topoi, with i♯ : O ⟶ underline{O}_X the obvious map. -/
@[stacks 08VA]
#check (AlgebraicGeometry.Scheme.CotangentSite.i :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)],
    RingedSite.ToposHom
      (AlgebraicGeometry.Scheme.CotangentSite.inverseImageRingedSite Λ X)
      (AlgebraicGeometry.Scheme.CotangentSite.ringedSite Λ X))

/- 92.25.1.1 (2): the morphism of ringed topoi
π : (Sh(C_{X/Λ}), underline{O}_X) ⟶ (Sh(X_Zar), O_X)
is induced by the forgetful functor u : C_{X/Λ} ⥤ X_Zar. -/
@[stacks 08VA]
#check (AlgebraicGeometry.Scheme.CotangentSite.toZariski :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)],
    RingedSite.ToposHom
      (AlgebraicGeometry.Scheme.CotangentSite.inverseImageRingedSite Λ X)
      (AlgebraicGeometry.Scheme.AssociatedModule.smallCommRingedSite .zariski X))
