/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AssociatedPlus

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 46.7.2: for an affine scheme `Spec A`, association realizes the
bounded-below derived category of adequate modules as the localization of the
bounded-below homotopy category of quasicoherent modules at universal
quasi-isomorphisms. -/
@[stacks 06ZR]
#check (SheafOfModules.Adeq.associatedPlusIsLocalization :
  ∀ (tau : StandardTopology) (A : CommRingCat.{u})
    [HasDerivedCategory.{u} (SheafOfModules.Adeq.affineAdeq tau A)],
    (SheafOfModules.Adeq.associatedAffineToBoundedBelowDerived tau A).IsLocalization
      (Scheme.QCoh.universalQuasiIso (Scheme.Spec.obj (op A))))
