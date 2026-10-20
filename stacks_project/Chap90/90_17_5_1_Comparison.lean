/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SelfPullbackComparison

open CategoryTheory

universe u

/- 90.17.5.1 The residue-plus-difference comparison identifies the self-pullback
with the square-zero pullback and preserves the first projection. -/
#check (ArtinianLocalAlgCat.selfPullbackIso :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {A A' : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (hI : IsLocalRing.maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥),
    ArtinianLocalAlgCat.selfPullback f ≅
      ArtinianLocalAlgCat.squareZeroPullback A' (ArtinianLocalAlgCat.kerModule f hI))
