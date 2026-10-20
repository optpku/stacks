/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SelfPullback

/-!
# Compatibility view of the self fibre product
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {A A' : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)

/- 90.17.5.2 self-pullback compatibility -/
#check (ArtinianLocalAlgCat.selfPullback_spec f :
  IsPullback (ArtinianLocalAlgCat.selfPullbackFst f)
      (ArtinianLocalAlgCat.selfPullbackSnd f) f f ∧
    ArtinianLocalAlgCat.selfPullbackToBase f = ArtinianLocalAlgCat.selfPullbackFst f ≫ f)
