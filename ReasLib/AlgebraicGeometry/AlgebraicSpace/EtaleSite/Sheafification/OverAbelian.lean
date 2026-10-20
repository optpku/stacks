/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.Abelian
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Abelian sheafification on slices of the small étale site

The slice basis consists of actual arrows from the small atlas charts to the
specified étale object. Native small-site sheafification and dense-subsite
right Kan extension keep the original coefficient universe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.SmallAtlas

/-- The arrows from the supplied small atlas charts cover the actual slice. -/
theorem over_coverDense {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : Over S) (a : ofOver U ⟶ X) [AlgebraicSpace.Etale a]
    (ha : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (V : smallEtaleSite X) :
    (CostructuredArrow.toOver (inclusion U a) V).IsCoverDense
      ((smallEtaleTopology X).over V) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.SmallAtlas

namespace AlgebraicGeometry.AlgebraicSpace

/-- Abelian sheafification on a slice uses the original small atlas arrows. -/
theorem smallEtaleOverAbelianSheafification {S : Scheme.{u}} (X : AlgebraicSpace S)
    (V : smallEtaleSite X) :
    HasWeakSheafify ((smallEtaleTopology X).over V) AddCommGrpCat.{u} := by
  let U := AtlasInput.scheme X
  let a := AtlasInput.map X
  letI : AlgebraicSpace.Etale a := AtlasInput.etale X
  let G := CostructuredArrow.toOver (PullbackFactory.SmallAtlas.inclusion U a) V
  let K := (smallEtaleTopology X).over V
  letI : G.IsCoverDense K :=
    PullbackFactory.SmallAtlas.over_coverDense U a (AtlasInput.locallySurjective X) V
  exact Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence
    (G.inducedTopology K) K G AddCommGrpCat.{u}

end AlgebraicGeometry.AlgebraicSpace
