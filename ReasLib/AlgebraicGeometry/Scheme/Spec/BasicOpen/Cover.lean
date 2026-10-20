/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

universe u

namespace AlgebraicGeometry.Spec.BasicOpenUnion

/-! # Covers by finite unions of principal opens -/

/-- The canonical cover of a finite union of principal open subsets by its constituents. -/
noncomputable def openCover {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    (⨆ i : Fin r, PrimeSpectrum.basicOpen (f i) :
      (AlgebraicGeometry.Spec (CommRingCat.of A)).Opens).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover (X := AlgebraicGeometry.Spec (CommRingCat.of A))
    (fun i : Fin r ↦ PrimeSpectrum.basicOpen (f i))

end AlgebraicGeometry.Spec.BasicOpenUnion
