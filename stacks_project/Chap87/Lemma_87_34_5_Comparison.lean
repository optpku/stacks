/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.EtaleSite

/-! # Completed-algebra comparison for the affine étale site

The comparison uses explicit reduction data and continuous maps of completed algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

#check (AlgebraicGeometry.FormalAlgebraicSpace.spfAffineEtaleOppEquiv hB :
  ∀ (R : FormalAlgebraicSpace.ReductionData (spf B hB).obj),
    Nonempty ((AlgebraicSpace.affineEtaleSite R.space)ᵒᵖ ≌ CommAlgCat.EtaleCompletion B))
