/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Artinian.Decomposition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/-
Lemma 28.10.5: A locally Noetherian scheme of dimension zero is the disjoint union, indexed by
all of its points, of the spectra of its Artinian local stalk rings.
-/
@[stacks 0AAX] #check
  (AlgebraicGeometry.isIso_stalkSpectrumCoproductTo_of_topologicalKrullDim_eq_zero :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      topologicalKrullDim X = 0 →
        CategoryTheory.IsIso (AlgebraicGeometry.stalkSpectrumCoproductTo X))

#check
  (AlgebraicGeometry.stalkSpectrumCoproduct :
    AlgebraicGeometry.Scheme.{u} → AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.stalkSpectrumCoproductTo :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.stalkSpectrumCoproduct X ⟶ X)

#check
  (AlgebraicGeometry.stalkSpectrumCoproductTo_def :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.stalkSpectrumCoproductTo X =
        CategoryTheory.Limits.Sigma.desc (fun x : X ↦ X.fromSpecStalk x))

#check
  (AlgebraicGeometry.stalkSpectrumCoproductTo_ι :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) (x : X),
      CategoryTheory.Limits.Sigma.ι
          (fun y : X ↦ AlgebraicGeometry.Spec (X.presheaf.stalk y)) x ≫
        AlgebraicGeometry.stalkSpectrumCoproductTo X =
          X.fromSpecStalk x)

#check
  (AlgebraicGeometry.IsLocallyArtinian.isArtinianRing_stalk :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyArtinian X] (x : X),
      IsArtinianRing (X.presheaf.stalk x))

#check
  (AlgebraicGeometry.IsLocallyArtinian.stalkSpectrumCoproductTo_isIso :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyArtinian X],
      CategoryTheory.IsIso (AlgebraicGeometry.stalkSpectrumCoproductTo X))

#check
  (AlgebraicGeometry.isArtinianRing_stalk_of_topologicalKrullDim_eq_zero :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
      (hXdim : topologicalKrullDim X = 0) (x : X),
        IsArtinianRing (X.presheaf.stalk x))
